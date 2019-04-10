# -*- coding: utf-8 -*-
# an algorithm framework for the service area problem 
# by Dr. Yunfeng Kong (yfkong@henu.edu.cn), Henan University, China
# March 15, 2019

#algorithm info
##noprint "An algorithm framework for the service area problem (AFSAP) v1.01. " 
##noprint "by Dr. Yunfeng Kong (yfkong@henu.edu.cn), Henan University, China."
##noprint "March 31, 2019."

import sys,os,random,time,copy,math,tempfile
import arcpy

#mip solver
mip_solvers=[] #MIP solvers supported 
mip_solver=''  #MIP solver "cplex", "cbc" or ""
try:
    import cplex
    ##noprint "CPLEX Python API: available!"
except: 
    ##noprint "CPLEX Python API: unavailable!"
    pass
try:
    import pulp
    s=pulp.solvers.CPLEX_CMD()
    if s.available()==False:
        ##noprint "PuLP CPLEX: unavailable!"
        pass
    else:
        mip_solvers.append('cplex')
        ##noprint "PulP CPLEX: available!"		
    s=pulp.solvers.COIN_CMD()
    if s.available()==False:
        pass
        ##noprint "PuLP CBC: unavailable!"
    else:
        mip_solvers.append('cbc')
        ##noprint "PuLP CBC: available!"	
except: 
    ##noprint "PulP: unavailable!"
    pass
if len(mip_solvers)>0: mip_solver=mip_solvers[0]
##noprint "MIP Solvers and the default solver:",mip_solvers, mip_solver

#instance info
nodes=[]
num_units=-1
nodedij=[]
node_neighbors=[]
total_pop=0
avg_dis_min=0.0
spatial_contiguity=1 # 0 no, 1 yes
#parameters for districting
num_districts=-1 # number of service areas/facilities
max_num_facility=999 
pop_dis_coeff=10000.0 #used in the objective function
NearFacilityList=[]
NumNearFacility=6

#current solution
centersID=[]
node_groups=[]
capacities=[]
facilityCandidate=[]
facilityCapacity=[]
facilityCost=[]
district_info=[] #[[0,0,0.0] for x in range(num_districts)] # solution
MAXNUMBER=9999999999.0
objective_overload=MAXNUMBER
obj_balance=MAXNUMBER
objective=MAXNUMBER
biobjective=MAXNUMBER
given_solution=0 #reserved
all_solutions=[]

#best solution in each start
best_solution =[] # node_groups[:]
best_centersID=[]
best_biobjective=MAXNUMBER
best_objective=MAXNUMBER
best_objective_overload = MAXNUMBER

#global best solution 
best_centers_global=[]
best_solution_global=[]
best_biobjective_global = MAXNUMBER
best_objective_global = MAXNUMBER
best_overload_global = MAXNUMBER
best_centersID_global=[]

#search statistics
time_check=0
time_check_edge_unit=0
time_spp=0
time_op0=0
time_op1=0
time_op2=0
time_op3=0
time_op4=0
time_repare=0
count_op0=0
count_op1=0
count_op2=0
count_op3=0
count_op4=0
check_count=0
improved=0
move_count=0

#search histry
region_pool = []
pool_index=[]
best_centers_pool=[]
centersPool=[]

#local search
acceptanceRule="hc" #solver name
operators_selected=[0,1,2] #0 one-unit move, 1 two-unit move, 2 three-unit move
multi_start_count=6 #population size for GA, ILS, VNS, LIS+VND
initial_solution_method=[0,1,2] #1 region growth, 10 allocation, 100 split allocation
SA_maxloops = 100 # maximum number of search loops for GA
op_random = 1 # operators used sequentially (0) or randomly(1)
last_loop_obj=0.0
mainloop=0
mutation_rate=0.01 
cross_methods=-1
adj_pop_loops=50 #<=0, auto set; or >0 
solution_similarity_limit=3.3
deviation=0.0
intial_deviation=0.5
SA_temperature=1.0
SA_coolingrate=0.995 #auto selection
init_temperature=1.0 #0.7

#spp modelling
is_spp_modeling=1 #0 no spp modelling, 1 modelling at the end, 2 modelling in case of local optimum
spp_loops=50  #<=0, auto set; or >0 


solver_time_limit=7200 #used for mip modeling
solver_mipgap=0.000000000001
heuristic_time_limit=300
seed =random.randint(0,10000)
random.seed(seed)
adjust_mutation_rate=1

#tabu list
tabuSearch=0  #0 no tabu list, 1 use tabu list
tabuLength=100
tabuList=[]

#connective: constraints on spatial contiguity? 1 for yes and 0 for no 

#record a region in current solution
def update_region_pool(rid):
    global pool_index
    global time_spp
    if is_spp_modeling<=0:
        return
    t=time.time()
    obj=district_info[rid][2]+district_info[rid][4]*avg_dis_min*pop_dis_coeff
    idx=int(obj*100000)
    if idx not in pool_index[rid]:
        ulist=[x for x in  range(num_units) if node_groups[x]==rid]
        pool_index[rid].append(idx)
        region_pool.append([ulist,district_info[rid][2],district_info[rid][4],rid])
    time_spp+=time.time()-t
    return

    
#record all regions in current solution
def update_region_pool_all():
    if is_spp_modeling<=0:
        return
    for rid in range (num_districts):
        update_region_pool(rid)

#check continuality of a solution (sol)
def check_solution_continuality_feasibility(sol):
    if spatial_contiguity==0: return 1
    feasible = 1
    for i in range (num_districts):
        if check_continuality_feasibility(sol,i) == 0:
            feasible=0  #infeas.
            break
    return feasible

#check continuality of a region (rid) in solution (sol)
def check_continuality_feasibility(sol,rid):
    global time_check
    global check_count
    if spatial_contiguity==0: return 1
    check_count+=1
    t=time.time()
    ulist1=[x for x in range(len(sol)) if sol[x]==rid and x!=centersID[rid]]
    ulist2=[centersID[rid]]
    #ulist2.append(ulist1.pop())
    for x in ulist2:
        for i in range(len(ulist1)):
            j=ulist1[i]
            if j in node_neighbors[x]:
                ulist2.append(j)
                ulist1[i]=-1
        ulist1=[x for x in ulist1 if x>=0]
    #ulist3=[x for x in ulist1 if x!=-1]
    
    time_check+=time.time()-t
    if len(ulist1)==0:          
        return 1  #feasible
    return 0    #infeasible


def check_ulist_continuality(ulist):
    if spatial_contiguity==0: return 1
    global time_check
    global check_count
    t=time.time()
    ulist1=ulist[:]
    ulist2=[]
    ulist2.append(ulist1.pop())
    check_count+=1
    for x in ulist2:
        for i in range(len(ulist1)):
            #if ulist1[i]==-1: continue
            if ulist1[i] in node_neighbors[x]:
                ulist2.append(ulist1[i])
                ulist1[i]=-1
        ulist1=[x for x in ulist1 if x>=0]         
    #ulist3=[x for x in ulist1 if x!=-1]
    time_check+=time.time()-t
    if len(ulist1)==0:          
        return 1  #feasible
    return 0    #infeasible

#return a list of edge units
def find_edge_units():
    ulist=[]
    for x in range(num_units):
        if x in centersID: continue
        for y in node_neighbors[x]:
            k=node_groups[x]		
            if node_groups[y] != k:
                ulist.append(x)
                break
    random.shuffle(ulist)
    return ulist

#return a list of edge units that having three or more neighor regions
def find_edge_units_2():
    ulist=[]
    for x in range(num_units):
        if x in centersID: continue
        rlist=[node_groups[y] for y in node_neighbors[x]]
        rlist.append(node_groups[x])
        rset=set(rlist)
        if len(rset)>2:
            ulist.append(x)
    random.shuffle(ulist)
    return ulist


#check an edge unit (uid)
def is_edge_unit(uid):
    global time_check_edge_unit
    #if spatial_contiguity==0: return 1
    if uid in centersID:
        return False
    t=time.time()
    rlist = [node_groups[x] for x in node_neighbors[uid]]
    #rlist.sort()
    time_check_edge_unit+=time.time()-t
    #if rlist[0]==rlist[-1]:
    if len(set(rlist))>1:
        return False
    return True

#update region information of the current solution
def update_district_info():
    global objective_overload
    global objective
    global biobjective
    global district_info
    global move_count
    global obj_balance
    for k in range(num_districts):
        district_info[k][0] = 0
        district_info[k][1] = 0
        district_info[k][2] = 0.0
        district_info[k][3] = 0
        district_info[k][4] = 0

    for k in range(num_districts):
        ulist=[x for x in range(num_units) if node_groups[x]==k]
        if len(ulist)<=0:
            ##noprint "region has no any unit", k
            continue
        ck=centersID[k]
        district_info[k][0] = len(ulist)
        district_info[k][1] = sum(nodes[x][3] for x in ulist)
        district_info[k][2] = sum(nodedij[x][ck]*nodes[x][3] for x in ulist)
        district_info[k][3] = capacities[k] #sum(nodes[x][5] for x in ulist)
        district_info[k][4] = district_info[k][1]-capacities[k] # -district_info[k][3]
        if district_info[k][4]<0:
            district_info[k][4] =0
        
    bal=sum(x[4] for x in district_info)
    objective=sum([x[2] for x in district_info])
    objective_overload=bal
    obj_balance=bal*1.0/total_pop
    biobjective=objective+objective_overload*avg_dis_min*pop_dis_coeff
    move_count+=1
    return

#find the fragmented units in the current solution
def find_frag_unit2():
    if spatial_contiguity==0: return []
    global time_check_edge_unit
    t=time.time()		
    frag_units=[]
    for k in range(num_districts):
        ulist1=[centersID[k]]
        ulist2=[x for x in range(num_units) if node_groups[x]==k and x!=centersID[k]]
        for x in ulist1:
            for y in node_neighbors[x]:
                if node_groups[y]==k and y not in ulist1 :
                    ulist1.append(y)
        for x in ulist2:
            if x not in ulist1:
                frag_units.append(x)
    random.shuffle(frag_units)
    time_check_edge_unit+=time.time()-t	
    return frag_units

def find_frag_unit():
    if spatial_contiguity==0: return []
    global time_check_edge_unit
    t=time.time()	
    frag_units=[]
    for k in range(num_districts):
        ulist2=[centersID[k]]
        ulist1=[x for x in range(num_units) if node_groups[x]==k and x!=centersID[k]]
        for x in ulist2:
            for i in range(len(ulist1)):
                if ulist1[i] in node_neighbors[x]:
                    ulist2.append(ulist1[i])
                    ulist1[i]=-1
            ulist1=[x for x in ulist1 if x>=0]
        for x in ulist1:  frag_units.append(x)
    random.shuffle(frag_units)
    time_check_edge_unit+=time.time()-t
    return frag_units	

#repare the fragmented solution
def repare_fragmented_solution():
    if spatial_contiguity==0: return
    global node_groups
    frag_units=find_frag_unit()
    for x in frag_units:
        node_groups[x]=-1
    repare_partial_solution()
    update_district_info()

#r&r method
#remove the edge units and reassign them
def r_r_perb_edge_units():
    ulist=find_edge_units_2()
    if len(ulist)==0:
        ulist=find_edge_units()
    random.shuffle(ulist)
    rn=0
    for x in ulist:
        if x not in centersID:
            node_groups[x]=-1
            rn+=1
        if rn>= num_units/10:  #10% of units 
            break
    #repare_partial_solution()
    if spatial_contiguity==1: repare_fragmented_solution()
    else: repare_partial_solution()

#r&r method
#remove 1/40 units arround an edge unit
def r_r_perb_location():
    ulist=[find_edge_units_2()[0]]
    if len(ulist)==0:
        ulist=[find_edge_units()[0]]
    pop=0
    for x in ulist:
        for y in node_neighbors[x]:
            if y in centersID:
                continue
            if y not in ulist:
                pop+=nodes[y][3]
                ulist.append(y)
            if len(ulist)>=num_units/40:
                break
            #if pop >= total_pop/num_districts:
            #    break
        if len(ulist)>=num_units/40:
            break
        #if pop >= total_pop/num_districts:
        #    break
    for x in ulist:
        if x not in centersID:
            node_groups[x]=-1
    if spatial_contiguity==1: repare_fragmented_solution()
    else: repare_partial_solution()

#r&r method
#overlay current and best solution
#remove fragmented units
def r_r_perb_overlay():
    sol_overlay=best_solution[:]
    ulist=[x for x in range(num_units) if sol_overlay[x]!=node_groups[x]]
    #centersID=best_centers_global[:]
    for x in ulist:
        if x in centersID:
            continue
        node_groups[x]=-1
    if spatial_contiguity==1: repare_fragmented_solution()
    else: repare_partial_solution()

#r&r method
#assign the removed units to solution
def repare_partial_solution():
    if spatial_contiguity!=1:
        repare_partial_solution_nonconnectivity()
        return
    loops=0
    update_district_info()
    ulist=[x for x in range(num_units) if node_groups[x]==-1] # units not assigned
    while 1:
        if len(ulist)==0:
            break
        neighbors = []
        for x in ulist:
            for y in node_neighbors[x]:
                if node_groups[y] >=0:
                    nb=[x,node_groups[y],0.0]
                    if nb not in neighbors:
                        neighbors.append(nb)
        if len(neighbors) <1:
            continue
        if len(neighbors) ==1:
            nid=neighbors[0][0]
            rid=neighbors[0][1]
            node_groups[nid] = rid
            ulist.remove(nid)
            update_district_info()
            continue
        for i in range(len(neighbors)):
            nid=neighbors[i][0]
            rid=neighbors[i][1]
            #gap=sum([nodes[x][3] for x in range(num_units) if node_groups[x]==rid])+ nodes[nid][3] - facilityCapacity[rid]
            gap= district_info[rid][1]+ nodes[nid][3] - capacities[rid]
            #if gap<=0: gap=0
            neighbors[i][2]=gap*avg_dis_min*pop_dis_coeff + nodedij[nid][centersID[rid]]*nodes[nid][3]
        neighbors.sort(key=lambda x:x[2])
        #idx=random.randint(0,1)
        r=random.random()
        idx=int(r*r*len(neighbors))
        if idx==len(neighbors): idx-=1
        nid=neighbors[idx][0]
        rid=neighbors[idx][1]
        node_groups[nid] = rid #update the solution
        ulist.remove(nid)
        update_district_info()
        loops+=1
    update_district_info()

def repare_partial_solution_nonconnectivity():
    loops=0
    update_district_info()
    ulist=[x for x in range(num_units) if node_groups[x]==-1] # units not assigned
    while 1:
        if len(ulist)==0:
            break
        neighbors = []
        for x in ulist:
            for y in NearFacilityList[x]:
                neighbors.append([x,y,0.0])
        if len(neighbors) <1:
            continue
        if len(neighbors) ==1:
            nid=neighbors[0][0]
            rid=neighbors[0][1]
            node_groups[nid] = rid
            ulist.remove(nid)
            update_district_info()
            continue
        for i in range(len(neighbors)):
            nid=neighbors[i][0]
            rid=neighbors[i][1]
            #gap=sum([nodes[x][3] for x in range(num_units) if node_groups[x]==rid])+ nodes[nid][3] - capacities[rid]
            gap= district_info[rid][1]+ nodes[nid][3] - capacities[rid]
            #if gap<=0: gap=0
            neighbors[i][2]=gap*avg_dis_min*pop_dis_coeff + nodedij[nid][centersID[rid]]*nodes[nid][3]
        neighbors.sort(key=lambda x:x[2])
        #idx=random.randint(0,1)
        r=random.random()
        idx=int(r*r*min(len(neighbors),3))
        if idx==len(neighbors): idx-=1
        nid=neighbors[idx][0]
        rid=neighbors[idx][1]
        node_groups[nid] = rid #update the solution
        ulist.remove(nid)
        update_district_info()
        loops+=1
    update_district_info()
   
#r&r method
#ruin a region and recreate it
def r_r_perb_district():
    k=random.randint(0, num_districts-1)
    ulist=[x for x in range(num_units) if node_groups[x]==k and x!=centersID[k]]
    for x in ulist:
        node_groups[x]=-1
    repare_partial_solution()
    #repare_fragmented_solution()
    #update_district_info()

def r_r_perb_mutation(rate):
    global node_groups
    mutation(rate)
    return
    ulist2=find_edge_units()
    num=int(num_units*rate)
    for x in ulist2:
        node_groups[x]=-1
        num-=1
        if num<=0:
            break
    if spatial_contiguity==1: repare_fragmented_solution()
    else: repare_partial_solution()

#update the best and the global best solution
#if the current solution is better than the best
def update_best_solution():
    global best_objective
    global best_biobjective
    global best_objective_overload
    global best_solution
    global best_centersID
    global best_overload_global
    global best_biobjective_global
    global best_objective_global
    global best_solution_global
    global best_centers_global
    global improved_loop
    global improved
    improve =0
    if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
        ##noprint "check_solution_continuality_feasibility!!!"
        return improve
    biobj=biobjective
    biobj_best=best_biobjective
    if biobj<=biobj_best:
        best_biobjective=biobj
        best_objective = objective
        best_objective_overload = objective_overload
        best_solution = node_groups[:]
        best_centersID=centersID[:]
        improved_loop=mainloop
        improve =1
        improved+=1
    if biobj<best_biobjective_global:
        best_biobjective_global=biobj
        best_centers_global=centersID[:]
        best_solution_global=best_solution[:]
        best_objective_global = objective
        best_overload_global = objective_overload
    return improve

#return the neighor regions of unit nid
def neighbor_regions(nid):
    #if spatial_contiguity!=1:
    #    return NearFacilityList[nid]
    rid=node_groups[nid]
    rlist=[node_groups[x] for x in node_neighbors[nid] if node_groups[x]!=rid]
    rlist2=list(set(rlist))
    #if rid in rlist2: rlist2.remove(rid)
    if len(rlist2)>2: random.shuffle(rlist2)
    return rlist2

#evaluate the possible moves
#return 0 or 1 according to the acceptance rule
#acceptance rule: sa, rrt, oba or others
dev_move_counter=0
sls_move_possibility=0.01

def isbetter(obj_old,obj_new,bal_old,bal_new):
    global dev_move_counter
    biobj_old=biobjective
    dis=objective-obj_old+obj_new
    biobj_new=dis+(objective_overload-bal_old+bal_new)*avg_dis_min*pop_dis_coeff
    if biobj_new<biobj_old-0.000001:
        return 1
    if acceptanceRule=="sa":
        if SA_temperature<0.0001: return 0
        minobj=min(last_loop_obj,biobj_old)
        p=math.exp(-(biobj_new-minobj)/minobj*num_units/SA_temperature)
        #p=math.exp(-(obj_new-obj_old)/obj_old*num_units/SA_temperature)
        if random.random()< p:  return 1
    if acceptanceRule=="sls":
        pop_dev=total_pop/num_units/2  #1/2 pop in a unit
        if bal_new-bal_old > pop_dev: return 0
        if random.random()<sls_move_possibility:
            dev_move_counter+=1
            return 1
    if acceptanceRule=="rrt":
        if biobj_new < best_biobjective*(1+deviation/num_units):
            dev_move_counter+=1
            return 1
    return 0

def update_tabu_iist(nid,rid):
    global tabuList #tabuLength
    tabuList.append([nid,rid])
    if len(tabuList)>tabuLength:
        del tabuList[0]
#move one edge unit to its neighbor region
def one_unit_move():
    #global district_info
    global node_groups
    global time_op0
    global count_op0
    global tabuList #tabuLength
    
    t=time.time()
    improve = 0
    ulist=find_edge_units()
    find_best_solution=0
    for n_id in ulist:
        #if is_edge_unit(n_id)==False: continue
        r_id = node_groups[n_id]
        for new_r_id in neighbor_regions(n_id):
            if tabuSearch==1 and [n_id,new_r_id] in tabuList: continue
            obj_new = nodedij[n_id][centersID[new_r_id]] *nodes[n_id][3]
            obj_old = nodedij[n_id][centersID[r_id]] *nodes[n_id][3]
            old_pop1=district_info[r_id][4]
            old_pop2=district_info[new_r_id][4]
            new_pop1=district_info[r_id][1]-nodes[n_id][3]
            if new_pop1 >capacities[r_id]: new_pop1-=capacities[r_id]
            else: new_pop1=0
            new_pop2=district_info[new_r_id][1]+nodes[n_id][3]
            if new_pop2 >capacities[new_r_id]:  new_pop2-=capacities[new_r_id]
            else: new_pop2=0
            #yfkong
            #if new_pop1+new_pop2 > old_pop1+old_pop2: continue
            if isbetter(obj_old,obj_new,old_pop1+old_pop2,new_pop1+new_pop2)==0:
                continue
            sol=node_groups[:]
            sol[n_id] = new_r_id
            if spatial_contiguity==1 and check_continuality_feasibility(sol,r_id)==0:
                break
            count_op0+=1
            node_groups[n_id] = new_r_id # solution
            if tabuSearch==1: update_tabu_iist(n_id,new_r_id)
            update_district_info()
            find_best_solution += update_best_solution()
            break
    time_op0+=time.time()-t
    return find_best_solution

#for a region
#move out one edge unit to its neighbor region, and
#move in one edge unit from its neighbor region
def two_unit_move():
    #global district_info
    global node_groups
    global time_op1
    global count_op1
    global tabuList
    t=time.time()
    find_best_solution=0
    improve = 0
    ulist=find_edge_units()
    movelist =[]
    for n_id1 in ulist:
        if n_id1 in movelist: continue
        #if is_edge_unit(n_id1)==False:
        #    movelist.append(n_id1)
        #    continue
        r_id1 = node_groups[n_id1]
        rlist1=neighbor_regions(n_id1)
        success_move=0
        for n_id2 in ulist:
            if n_id1 == n_id2: continue
            if n_id1 in movelist: break
            if n_id2 in movelist: continue
            #if is_edge_unit(n_id2)==False:
            #    movelist.append(n_id2)
            #    continue
            if node_groups[n_id2] not in rlist1:
                continue
            new_r_id1=node_groups[n_id2]
            if tabuSearch==1 and [n_id1,new_r_id1] in tabuList: continue
            r_id2 = node_groups[n_id2]

            for new_r_id2 in neighbor_regions(n_id2):
                if tabuSearch==1 and [n_id2,new_r_id2] in tabuList: continue
                obj_new = nodedij[n_id1][centersID[new_r_id1]]*nodes[n_id1][3] + nodedij[n_id2][centersID[new_r_id2]] *nodes[n_id2][3]
                obj_old = nodedij[n_id1][centersID[r_id1]]*nodes[n_id1][3]+nodedij[n_id2][centersID[r_id2]] *nodes[n_id2][3]

                new_district_info = [x[1] for x in district_info]
                new_district_info[r_id1] -= nodes[n_id1][3]
                new_district_info[r_id2] -= nodes[n_id2][3]
                new_district_info[new_r_id1] += nodes[n_id1][3]
                new_district_info[new_r_id2] += nodes[n_id2][3]                
                bal=0
                bal=sum(new_district_info[x]-capacities[x] for x in range(num_districts) if new_district_info[x]>capacities[x])
                #yfkong
                #if bal>objective_overload: continue
                if isbetter(obj_old,obj_new,objective_overload,bal)==0:
                    continue

                sol=node_groups[:]
                sol[n_id1] = new_r_id1
                sol[n_id2] = new_r_id2
                if spatial_contiguity==1 and check_continuality_feasibility(sol,r_id1)==0:
                    movelist.append(n_id1)
                    break
                    
                if spatial_contiguity==1 and check_continuality_feasibility(sol,r_id2)==0:
                    movelist.append(n_id2)
                    break

                count_op1+=1
                node_groups[n_id1] = new_r_id1
                node_groups[n_id2] = new_r_id2
                if tabuSearch==1:
                    update_tabu_iist(n_id1,new_r_id1)
                    update_tabu_iist(n_id2,new_r_id2)
                #obj=biobjective
                update_district_info()
                #movelist.append(n_id1)
                #movelist.append(n_id2)
                find_best_solution += update_best_solution()
                success_move=1
                break
            if success_move==1: break            
    time_op1+=time.time()-t
    return find_best_solution
#move three units
def three_unit_move():
    global node_groups
    global tabuList
    global time_op4
    global count_op4
    t=time.time()
    find_best_solution=0
    improve = 0
    ulist=find_edge_units()
    new_r_id1 = MAXNUMBER
    new_r_id2 = MAXNUMBER
    new_r_id3 = MAXNUMBER
    r_id1 = MAXNUMBER
    r_id2 = MAXNUMBER
    r_id3 = MAXNUMBER
    movelist=[]
    for n_id1 in ulist:
        if n_id1 in movelist: continue
        r_id1=node_groups[n_id1]
        improve=0
        for n_id2 in ulist:
            if n_id1 == n_id2: continue
            if n_id1 in movelist: break
            if n_id2 in movelist: continue
            if node_groups[n_id2] not in neighbor_regions(n_id1): continue
            new_r_id1=node_groups[n_id2]
            if tabuSearch==1 and [n_id1,new_r_id1] in tabuList: continue
#            if is_edge_unit(n_id2)==False:
#                movelist.append(n_id2)
#                continue
            r_id2=node_groups[n_id2]
            for n_id3 in ulist:
                if n_id1 == n_id3 or n_id2 == n_id3:continue
                if n_id1 in movelist: break
                if n_id2 in movelist: break
                if n_id3 in movelist: continue
                if node_groups[n_id3] not in neighbor_regions(n_id2): continue
#                if is_edge_unit(n_id3)==False:
#                    movelist.append(n_id3)
#                    continue
                new_r_id2=node_groups[n_id3]
                if tabuSearch==1 and [n_id2,new_r_id2] in tabuList: continue
                r_id3=node_groups[n_id3]
                for new_r_id3 in neighbor_regions(n_id3):
                    if tabuSearch==1 and [n_id3,new_r_id3] in tabuList: continue
                    obj_new =nodedij[n_id1][centersID[new_r_id1]]*nodes[n_id1][3] + nodedij[n_id2][centersID[new_r_id2]]*nodes[n_id2][3] + nodedij[n_id3][centersID[new_r_id3]]*nodes[n_id3][3]
                    obj_old =nodedij[n_id1][centersID[r_id1]]    *nodes[n_id1][3] + nodedij[n_id2][centersID[r_id2]]    *nodes[n_id2][3] + nodedij[n_id3][centersID[r_id3]]    *nodes[n_id3][3]
                    new_district_info = [x[1] for x in district_info]
                    new_district_info[r_id1] -= nodes[n_id1][3]
                    new_district_info[r_id2] -= nodes[n_id2][3]
                    new_district_info[r_id3] -= nodes[n_id3][3]
                    new_district_info[new_r_id1] += nodes[n_id1][3]
                    new_district_info[new_r_id2] += nodes[n_id2][3]
                    new_district_info[new_r_id3] += nodes[n_id3][3]
                    bal=0
                    
                    bal=sum(new_district_info[x]-capacities[x] for x in range(num_districts) if new_district_info[x]>capacities[x])
                    #yfkong
                    #if bal>objective_overload: continue
                    if isbetter(obj_old,obj_new,objective_overload,bal)==0:
                        continue
                    rlist=[r_id1,r_id2,r_id3,new_r_id1,new_r_id2,new_r_id3]
                    sol=node_groups[:]
                    sol[n_id1] = new_r_id1
                    sol[n_id2] = new_r_id2
                    sol[n_id3] = new_r_id3
                    if spatial_contiguity==1 and check_continuality_feasibility(sol,r_id1)==0:
                        movelist.append(n_id1)
                        break
                    if spatial_contiguity==1 and r_id1!=r_id2 and check_continuality_feasibility(sol,r_id2)==0:
                        movelist.append(n_id2)
                        break
                    if spatial_contiguity==1 and r_id1!=r_id3 and r_id2!=r_id3 and check_continuality_feasibility(sol,r_id3)==0:
                        movelist.append(n_id3)
                        break
                    count_op4+=1
                    node_groups[n_id1] = new_r_id1
                    node_groups[n_id2] = new_r_id2
                    node_groups[n_id3] = new_r_id3
                    if tabuSearch==1:
                        update_tabu_iist(n_id1,new_r_id1)
                        update_tabu_iist(n_id2,new_r_id2)
                        update_tabu_iist(n_id3,new_r_id3)

                    #movelist.append(n_id1)
                    #movelist.append(n_id2)
                    #movelist.append(n_id3)
                    obj=biobjective
                    update_district_info()
                    improve = 1
                    find_best_solution +=  update_best_solution()
                    break
                if improve == 1:
                    break
            if improve == 1:
                break
    time_op4+=time.time()-t
    return find_best_solution

# local search
def RRT_local_search():
    global improved
    #global node_neighbors
    improved=0
    #operators=[0,1,2,3,4]
    operators=operators_selected[:]
    if op_random == 1 and random.random()>0.5:
        random.shuffle(operators)
    for op in operators:
        if op == 0:
            one_unit_move()
            #update_region_pool_all()
        if op == 1:
            two_unit_move()
            #update_region_pool_all()
        if op == 2:
            #if random.random()<0.1: three_unit_move()
            three_unit_move()
            #update_region_pool_all()
    return

#local search with operator op
def vnd_op_search(op):
    #global node_neighbors
    #for x in node_neighbors:
    #    random.shuffle(x)
    if op == 0:
        one_unit_move()
    if op == 1:
        two_unit_move()
    if op == 2:
        three_unit_move()
    return

#VND search
def VND_local_search():
    global improved
    improved=0
    #operators=[0,1,2,3,4]
    operators=operators_selected[:]    
    #if op_random == 1:
    if op_random == 1 and random.random()>0.5:
        random.shuffle(operators)
    obj=biobjective
    while 1:
        vnd_op_search(operators[0])
        if abs(biobjective-obj)>0.00001:
            obj=biobjective
            continue
        if len(operators)==1:break
        vnd_op_search(operators[1])
        if abs(biobjective-obj)>0.00001:
            obj=biobjective
            continue
        if len(operators)==2:break

        vnd_op_search(operators[2])
        if abs(biobjective-obj)>0.00001:
            obj=biobjective
            continue
        if len(operators)==3:break
        vnd_op_search(operators[3])
        if abs(biobjective-obj)>0.00001:
            obj=biobjective
            continue
        if len(operators)==4:break
        vnd_op_search(operators[4])
        if abs(biobjective-obj)>0.00001:
            obj=biobjective
            continue
        break
    return

#VNs search
def vns_op_search(op):
    #global node_neighbors
    global node_groups
    node_groups=best_solution[:]
    update_district_info()
    obj=biobjective
    shake(op+1)
    VND_local_search()
    update_region_pool_all()
    return obj-biobjective

def shake(k):
    global node_groups
    if k<1: return
    ulist=find_edge_units()
    counter=0
    for uid in ulist:#(int(num_units*rate+0.5)):
        rid=node_groups[uid]
        r=neighbor_regions(uid)
        if len(r)<1: continue
        random.shuffle(r)
        node_groups[uid]=r[0]
        counter+=1
        if counter>=k: break
    if spatial_contiguity==1: repare_fragmented_solution()
    else: update_district_info()
    

def VNS_local_search():
    global improved
    improved=0
    operators=operators_selected[:]
    count=0
    while 1:
        count+=1
        objimprove=vns_op_search(operators[0])
        if objimprove>0.00001:  continue
        if len(operators)==1:break

        count+=1
        objimprove=vns_op_search(operators[1])
        if objimprove>0.00001:  continue
        if len(operators)==2:break

        count+=1
        objimprove=vns_op_search(operators[2])
        if objimprove>0.00001: continue
        break
    return

#read instance file, f1:unit info, f2: connectivity info
def readfile(f1,f2):
    global num_units
    global total_pop
    global nodes
    global node_neighbors
    global nodedij
    global capacities
    global centersID
    global facilityCandidate
    global facilityCapacity
    global facilityCost
    
    global facilityCost
    global num_districts
    global district_info
    global avg_dis_min
    node =[0,0,0,0,0,0,0,0,0,0]
    #school_nodes = []
    nodes = []
    #nodes.append(node)
    ##noprint "reading nodes ...",
    f = open(f1)
    line = f.readline()  #OID	pop	PointX	PointY	fcadidature	fcost	fcapacity
    line = f.readline()
    nodeidx=0
    while line:
        line=line[0:-1]
        items = line.split(',')
        if len(items)<=2:
            items = line.split('\t')
        unit=[nodeidx, float(items[2]), float(items[3]), int(items[1]),int(items[0]),int(items[6]),int(items[4]),int(items[5])]
        nodes.append(unit)
        nodeidx+=1
        #nodes.append([int(items[1]), float(items[8]), float(items[9]), int(items[5]), int(items[6]), int(items[7]),int(items[12]),int(items[13])])
        line = f.readline()
    f.close()
    num_units=len(nodes)
    total_pop=sum(x[3] for x in nodes)
    ##noprint num_units,"units"
    ##noprint "reading connectivity ...",
    connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]
    ###id1,id2#####
    f = open(f2)
    line = f.readline()             # 调用文件的 readline()方法
    line = f.readline()
    links=0
    while line:
        items = line.split(',')
        if len(items)<=2:
            items = line.split('\t')
        if int (items[1]) != int (items[2]):
            id1=int (items[1])
            id2=int (items[2])
            idx1=-1
            idx2=-1
            for i in range(num_units):
                if nodes[i][4]==id1:
                    idx1=i
                if nodes[i][4]==id2:
                    idx2=i
                if idx1>=0 and idx2>0:
                    break
            connectivity[idx1][idx2]=1
            connectivity[idx2][idx1]=1
            links+=1
        line = f.readline()
    f.close()
    ##noprint links,"links"

    nodedij=[[MAXNUMBER for x in range(len(nodes))] for y in range(len(nodes))]
    max_dij=0.0
    for i in range(len(nodes)):
        for j in range(i,len(nodes)):
            if j==i:
                nodedij[i][j]=0
                continue
            d2=pow(nodes[i][1]-nodes[j][1],2)
            d2+=pow(nodes[i][2]-nodes[j][2],2)
            d=pow(d2,0.5)/1000
            nodedij[i][j]=d
            nodedij[j][i]=d
            if d>max_dij:
                max_dij=d

    node_neighbors = [[]for x in range(len(nodes))]
    for i in range(len(nodes)):
        for j in range(len(nodes)):
            if j<=i:
                continue
            if connectivity[i][j]==1:
                node_neighbors[i].append(j)
                node_neighbors[j].append(i)

    num_units=len(nodes)
    facilityCandidate=[]
    facilityCapacity=[]
    facilityCost=[]
    centersID=[]
    ##noprint "all data are read! "
    for i in range(num_units):
        if nodes[i][5]>0:
            facilityCandidate.append(i)
            facilityCapacity.append(nodes[i][5])
            facilityCost.append(nodes[i][7])
            centersID.append(i)

    facilityCandidate.sort()
    centersID=[]
    capacities=[]
    for x in facilityCandidate:
        centersID.append(x)
        capacities.append(nodes[x][5])
    num_districts=len(centersID)
    district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
    dis=0.0
    for i in range(num_units):
        d=MAXNUMBER
        for k in facilityCandidate:
            if nodedij[i][k]<d:
                d=nodedij[i][k]
        dis+=d*nodes[i][3]
    avg_dis_min=dis/total_pop
    ##noprint "the total and averaged nearst distance to facility",dis,avg_dis_min
    ##noprint "demand and supply",total_pop,sum(facilityCapacity)
    find_NearFacilityList(NumNearFacility)

def initialize_instance():
    global total_pop
    global num_units
    global num_districts
    global district_info
    global avg_dis_min
    total_pop=sum(x[3] for x in nodes)
    num_units=len(nodes)
    num_districts=len(centersID)
    district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
    dis=0.0
    for i in range(num_units):
        d=MAXNUMBER
        for k in centersID:
            if nodedij[i][k]<d:
                d=nodedij[i][k]
        dis+=d*nodes[i][3]
    avg_dis_min=dis/total_pop
    find_NearFacilityList(NumNearFacility)
    arcpy.AddMessage("total demand: "+str(total_pop))
    arcpy.AddMessage("total supply: "+str(sum(x[5] for x in nodes)))
    arcpy.AddMessage("avg. distance to nearest facility: "+str(avg_dis_min))
    
#read network distance
def readdistance(dfile):
    global nodedij
    nodedij=[[MAXNUMBER for x in range(len(nodes))] for y in range(len(nodes))]
    ##noprint "reading distances ...",
    f = open(dfile)
    line = f.readline()             # 调用文件的 readline()方法
    line = f.readline()
    while line:
        items = line.split(',')
        if len(items)<=2:
            items = line.split('\t')
        if int (items[1]) != int (items[2]):
            id1=int (items[1])
            id2=int (items[2])
            idx1=-1
            idx2=-1
            for i in range(num_units):
                if nodes[i][4]==id1:
                    idx1=i
                if nodes[i][4]==id2:
                    idx2=i
                if idx1>=0 and idx2>0:
                    break
            if idx1>=0 and idx2>=0:
                nodedij[idx1][idx2]=float(items[3])
        line = f.readline()
    f.close()
    find_NearFacilityList(NumNearFacility)

def find_NearFacilityList(nnn):
    global NearFacilityList
    NearFacilityList=[]
    n=nnn
    if n>num_districts: n=num_districts
    for i in range(num_units):
        fdlist=[ [x,nodedij[i][centersID[x]]] for x in range(num_districts)]
        fdlist.sort(key=lambda x:x[1])
        flist=[x[0] for x in fdlist[0:n]]
        NearFacilityList.append(flist)

##def location_model(numf):
##    global node_groups
##    global centersID
##    global num_districts
##    global capacities
##    global district_info
###    facilityCandidate=[]
###    facilityCapacity=[]
###    facilityCost=[]
##    
##    prob = pulp.LpProblem("location",pulp.LpMinimize)
##    xvariables={}
##    costs={}
##    alpha_coeff=avg_dis_min*pop_dis_coeff
##    for i in range(num_units):
##        for j in facilityCandidate:
##            xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
##            costs["x_" +str(i)+ "_"+ str(j)]=nodedij[i][j]*nodes[i][3]*(random.random()+49.5)/50
##    yvariables={}
##    for i in facilityCandidate:
##        yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
##        costs["y_" +str(i)]=nodes[i][7]
##    obj=""
##    for x in xvariables:
##        obj += costs[x]*xvariables[x]
##    for y in yvariables:
##        if costs[y]>0:
##            obj += costs[y]*yvariables[y]
##    prob +=obj
##
####    for k in facilityCandidate:
####        if nodes[k][6]!=1:
####            continue
####        s=xvariables["x_" +str(k)+ "_"+ str(k)]
####        prob +=s == 1
##    for k in facilityCandidate:
##        if nodes[k][6]==1:
##            s=yvariables["y_" +str(k)]
##            prob +=s == 1
##
##    s=""
##    for k in facilityCandidate:
##        s+=yvariables["y_" +str(k)]
##    prob +=s <= numf
##
##    for i in range(num_units):
##        s=""
##        for j in facilityCandidate:
##            s+=xvariables["x_" +str(i)+ "_"+ str(j)]
##        prob +=s == 1
##
##    for k in facilityCandidate:
##        s=""
##        for i in range(num_units):
##            s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]
##        s-=nodes[k][5] * yvariables["y_" +str(k)]
##        prob+=s <= 0
##        
##    prob.writeLP("_location.lp")
##    cbc=pulp.solvers.COIN_CMD(mip=1,msg=1,maxSeconds=10,fracGap = 0.0005)
##    if mip_solver=='cplex':
##        cbc=pulp.solvers.CPLEX_CMD(options=['set mip tolerances mipgap 0.0005'])
##    cbc.actualSolve(prob)
##
##    if prob.status<0:
##        ##noprint "model unsolved..."
##        return -1
##    sol=[]
##    centersID=[]
##    for v in prob.variables():
##        if (v.varValue >= 0.90):
##            ###noprint v,v.varValue
##            items=v.name.split('_')
##            i=int(items[1])
##            if items[0]=='y':
##                centersID.append(i)
##                continue
##            k=int(items[2])
##            sol.append([i,k])
##    ###noprint sol
##    num_districts=len(centersID)
##    district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
##    centersID.sort()
##    node_groups=[-1 for x in range(num_units)]
##    for i in range(len(sol)):
##        node_groups[sol[i][0]]=sol[i][1]
##    for k in range(num_districts):
##        ck=centersID[k]
##        for i in range(num_units):
##            if node_groups[i]==ck:
##                node_groups[i]=k
##    capacities=[]
##    for x in centersID:
##        capacities.append(nodes[x][5])
##    return 

def location_model_lp(numf):
    global node_groups
    global centersID
    global num_districts
    global capacities
    global district_info
#    facilityCandidate=[]
#    facilityCapacity=[]
#    facilityCost=[]
    
    prob = pulp.LpProblem("location",pulp.LpMinimize)
    xvariables={}
    costs={}
    alpha_coeff=avg_dis_min*pop_dis_coeff
    for i in range(num_units):
        for j in facilityCandidate:
            xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, None, pulp.LpInteger)
            costs["x_" +str(i)+ "_"+ str(j)]=nodedij[i][j] #*(random.random()+49.5)/50
    yvariables={}
    for i in facilityCandidate:
        yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
        costs["y_" +str(i)]=nodes[i][7]
    obj=""
    for x in xvariables:
        obj += costs[x]*xvariables[x]
    #for y in yvariables:
    #    if costs[y]>0:
    #        obj += costs[y]*yvariables[y]
    prob +=obj

    for k in facilityCandidate:
        #if nodes[k][6]!=1:
        #    continue
        s=xvariables["x_" +str(k)+ "_"+ str(k)]
        prob +=s == nodes[k][3]

##    for k in facilityCandidate:
##        if nodes[k][6]==1:
##            s=yvariables["y_" +str(k)]
##            prob +=s == 1

    s=""
    for k in facilityCandidate:
        s+=yvariables["y_" +str(k)]
    prob +=s <= numf

    for i in range(num_units):
        s=""
        for j in facilityCandidate:
            s+=xvariables["x_" +str(i)+ "_"+ str(j)]
        prob +=s == nodes[i][3]

    for k in facilityCandidate:
        s=""
        for i in range(num_units):
            s+=xvariables["x_" +str(i)+ "_"+ str(k)]
        s-=nodes[k][5] * yvariables["y_" +str(k)]
        prob+=s <= 0
        
    #prob.writeLP("_location.lp")
    cbc=pulp.solvers.COIN_CMD(mip=1,msg=1,maxSeconds=10,fracGap = 0.00001)
    #prob.solve(solver=cbc)
    if mip_solver=='cplex':
        cbc=pulp.solvers.CPLEX_CMD(options=['set mip tolerances mipgap 0.00001'])
    cbc.actualSolve(prob)

    if prob.status<0:
        ##noprint "model unsolved..."
        return -1
    sol=[]
    centersID=[]
    for v in prob.variables():
        if (v.varValue >= 0.90):
            ###noprint v,v.varValue
            items=v.name.split('_')
            i=int(items[1])
            if items[0]=='y':
                centersID.append(i)
                continue
            k=int(items[2])
            sol.append([i,k])
    num_districts=len(centersID)
    district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
    centersID.sort()
    node_groups=[-1 for x in range(num_units)]
    for i in range(len(sol)):
        node_groups[sol[i][0]]=sol[i][1]
    for k in range(num_districts):
        ck=centersID[k]
        for i in range(num_units):
            if node_groups[i]==ck:
                node_groups[i]=k
    capacities=[]
    for x in centersID:
        capacities.append(nodes[x][5])
    return pulp.value(prob.objective)

#build and solve a mip model 
def mipmodel():
    try:
        import cplex
    except:
        ##noprint "cplex is not supported"
        pass
        #return
    #import cplex
    global node_groups
    global centersID
    centers=centersID[:]
    
    node_groups=[-1 for i in range(num_units)]
    sta=init_sol_model2(0) #int
    if sta<0:
        node_groups=[-1 for i in range(num_units)]
        for k in range(num_districts):
            node_groups[centersID[k]]=k
        repare_partial_solution()
    else:
        repare_fragmented_solution()
    RRT_local_search()
    RRT_local_search()

    mip_mst_file=tempfile.mkstemp()[1]+".mst"
    f = open(mip_mst_file,"w")
    f.write('<?xml version = "1.0" encoding="UTF-8" standalone="yes"?>\n')
    f.write('<CPLEXSolutions version="1.2">\n')

    f.write(' <CPLEXSolution version="1.2">\n')
    f.write('  <header\n')
    f.write('    problemName=""\n')
    f.write('    solutionName="m0"\n')
    f.write('    solutionIndex="0"/>\n')
    f.write('  <variables>\n')
    idx=0
    for i in range(num_units):
        for k in range(num_districts):
            if node_groups[i]==k:
                s='   <variable name="' + 'y_'+str(i)+ '_'+ str(k)+ '" index="'+str(idx) + '" value="1"/>\n'
            else:
                s='   <variable name="' + 'y_'+str(i)+ '_'+ str(k)+ '" index="'+str(idx) + '" value="0"/>\n'
            f.write(s)
            idx+=1
##    for i in range(num_units):
##        for k in range(num_districts):
##            if centersID[k]==i:
##                s='   <variable name="' + 'w_'+str(i)+ '_'+ str(k)+ '" index="'+str(idx) + '" value="1"/>\n'
##            else:
##                s='   <variable name="' + 'w_'+str(i)+ '_'+ str(k)+ '" index="'+str(idx) + '" value="0"/>\n'
##            f.write(s)
##            idx+=1
    f.write('  </variables>\n')
    f.write(' </CPLEXSolution>\n')
    f.write('</CPLEXSolutions>\n')
    f.flush()
    f.close()


    alpha_coeff=avg_dis_min*pop_dis_coeff    
    mip_file=tempfile.mkstemp()[1]+".lp"
    f = open(mip_file,"w")
    f.write("Minimize\nobj: ")
    for k in range(num_districts):
        f.write(str(alpha_coeff) + " H_" + str(k) + " + ")
    objfunc=""
    for i in range(num_units):
        for k in range(num_districts):
            #if i==centers[k]:  continue
            objfunc+= str (nodes[i][3]*nodedij[i][centers[k]])
            objfunc+= " y_" +str(i)+ "_"+ str(k) + " + "
    f.write(objfunc[:-3])
    f.write("\nsubject to\n")
    #con 1
    cidx=0
    for i in range(num_units):
        f.write("c"+str(cidx)+":")
        cidx+=1
        s=""
        for k in range(num_districts):
            s+=" y_" +str(i)+ "_"+ str(k) +" + "
        f.write(s[:-3] + " = 1\n" )
    #con 2
    for k in range(num_districts):
        s=" "
        for i in range(num_units):
            s+=  str(nodes[i][3]) + " y_" +str(i)+ "_"+ str(k) + " + "
        f.write("c"+str(cidx)+":")
        cidx+=1
        f.write(s[:-3] + " - H_"+str(k) + " <= " + str(capacities[k])+"\n")

    #con 3
    for i in range(num_units):
        for j in node_neighbors[i]:
            for k in range(num_districts):
                f.write("c"+str(cidx)+":")
                cidx+=1
                s=" f_" +str(i)+ "_"+str(j)+ "_"+ str(k) +" - "
                s+= str(num_units-num_districts) + " y_" +str(i)+ "_"+ str(k)
                f.write(s + " <= 0\n")
    #con 4
    for i in range(num_units):
        for j in node_neighbors[i]:
            for k in range(num_districts):
                f.write("c"+str(cidx)+":")
                cidx+=1
                s=" f_" +str(i)+ "_"+str(j)+ "_"+ str(k) +" - "
                s+= str(num_units-num_districts) + " y_" +str(j)+ "_"+ str(k)
                f.write(s + " <= 0\n")
    #con 5
    for i in range(num_units):
        if i in centersID: continue
        for k in range(num_districts):
            f.write("c"+str(cidx)+":")
            cidx+=1
            s=""
            for j in node_neighbors[i]:
                s+=" f_" +str(i)+ "_"+str(j)+ "_"+ str(k) +" - " +" f_" +str(j)+ "_"+str(i)+ "_"+ str(k) + " + "
            f.write(s[:-2] + " - y_" +str(i)+ "_"+ str(k) + " >= 0\n")

            #f.write("c"+str(cidx)+":")
            #cidx+=1
            #f.write(s[:-2] + " <= 1\n")

##    #con 6
##    for i in range(num_districts):
##        i1=centersID[i]
##        for k in range(num_districts):
##            f.write("c"+str(cidx)+":")
##            cidx+=1
##            s=""
##            for j in node_neighbors[i1]:
##                s+=" f_" +str(i1)+ "_"+str(j)+ "_"+ str(k) +" - " +" f_" +str(j)+ "_"+str(i1)+ "_"+ str(k) + " + "
##            f.write(s[:-2] + " >= " + str(num_districts-num_units) + "\n")

    #con 6
    for i in centersID:
        for j in node_neighbors[i]:
            for k in range(num_districts):
                f.write("c"+str(cidx)+":")
                cidx+=1
                s=" f_" +str(i)+ "_"+str(j)+ "_"+ str(k) +" = 0 \n"
                f.write(s)

    for k in range(num_districts):
        f.write("c"+str(cidx)+":")
        cidx+=1
        f.write(" y_"+str(centers[k]) + "_" + str(k) + " = 1\n")

##    for k in range(num_districts):
##        f.write("c"+str(cidx)+":")
##        cidx+=1
##        f.write(" H_"+ str(k) + " = 0\n")


##    ulist=non_near_list(100)
##    for x in ulist:
##        if node_groups[x[0]] == x[1]: continue
##        f.write("c"+str(cidx)+":")
##        cidx+=1
##        f.write(" y_"+str(x[0]) + "_" + str(x[1]) + " = 0\n")

    f.write("Binaries\n")
    for i in range(num_units):
        for k in range(num_districts):
            f.write(" y_" +str(i)+ "_"+ str(k)+"\n")
##    for i in range(num_units):
##        for k in range(num_districts):
##            f.write(" w_" +str(i)+ "_"+ str(k)+"\n")
          
    f.write("Generals\n")
    for k in range(num_districts):
        #f.write(" H_" + str(k) + "\n" + " L_"+ str(k) + "\n")
        f.write(" H_" + str(k) + "\n")
    for i in range(num_units):
        for j in node_neighbors[i]:
            for k in range(num_districts):
                f.write(" f_" +str(i)+ "_"+str(j)+ "_"+ str(k)+"\n")
    f.write("End\n")
    f.flush()
    f.close()

    tstart=time.time()
    c = cplex.Cplex()
    c.parameters.mip.tolerances.mipgap.set(solver_mipgap)
    c.parameters.timelimit.set(solver_time_limit)
    #c.parameters.threads.set(4)
    c.parameters.parallel.set(-1)
    c.parameters.mip.display.set(2)
    c.read(mip_file)
    c.MIP_starts.read(mip_mst_file)
    c.solve()
    #if os.path.isfile(mip_file): os.remove(mip_file)
    #if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)

    #c.populate_solution_pool()
    #c.populate_solution_pool()
    ##noprint "cplex status and obj:",c.solution.get_status_string(),c.solution.get_objective_value()
    snames = c.solution.pool.get_names()
    for sln in range(1):
        sol=[[0,0,-1] for x in range(num_units)]
        for i in range(num_units):
            sol[i][0]=nodes[i][0]
            for k in range(num_districts):
                var="y_" +str(i)+ "_"+ str(k)
                #yik=c.solution.get_values(var)
                yik=c.solution.pool.get_values(sln, var)
                if yik>0.9:
                    node_groups[i]=k
                #var="w_" +str(i)+ "_"+ str(k)
                #wik=c.solution.get_values(var)
                #if wik>0.9:
                #    centersID[k]=i
    update_district_info()
    update_best_solution()
    ##noprint "model solution",biobjective,objective,objective_overload,time.time()-tstart
    
#set solver parameters
#solver: "hc", "vnd","sa", "oba", "ils", "ga", "mip","vns","hyb"
#start: number of multistarts
#loops: number of loops for local search, not used by hc, vnd and mip
#spp: 1 for addtional spp modeling, not used by mip
#s: random seed (-1, select random seed)
def set_beta(b):
    global pop_dis_coeff
    pop_dis_coeff=b

def set_ls_operators(ops):
    global operators_selected
    operators_selected=ops[:]

def set_initial_method(mthds):
    global initial_solution_method
    initial_solution_method=mthds
def set_mutation_rate(r):
    global mutation_rate
    mutation_rate=r
    
def set_solver_params(numf,solver,start,timelimit,spp,s):
    global multi_start_count
    global SA_maxloops
    global heuristic_time_limit
    global seed
    global acceptanceRule
    global is_spp_modeling
    global max_num_facility
    global tabuLength
    max_num_facility=numf
    is_spp_modeling=spp
    if acceptanceRule=='mip':
        is_spp_modeling=0
    if solver not in ["hc","sls", "vnd","sa", "ils", "rrt", "mip","vns","ilsvnd"]:
        ##noprint "Invalid solver!"
        return
    acceptanceRule=solver
    multi_start_count=start
    if start<=0:
        multi_start_count=1
    heuristic_time_limit=timelimit
    #SA_maxloops=loops
    seed=s
    #if seed<0:
    #    seed=random.randint(0,100)
    #    #random.seed(s)
    #if loops<=0:
    #    SA_maxloops=1
    is_spp_modeling=spp
    if numf != len(centersID):
        ##noprint "invalid number of facilities"
        return
    tabuLength=max(numf,num_units/10)
    #return solve()

def solve():
    global multi_start_count
    global SA_maxloops
    global seed
    global acceptanceRule
    global best_objective
    global best_biobjective
    global best_objective_overload
    global best_biobjective_global
    global objective
    global biobjective
    global objective_overload
    global SA_temperature
    global SA_coolingrate
    global deviation
    global node_groups
    global centersID
    #global node_neighbors
    global acceptanceRule
    global move_count
    global last_loop_obj
    global region_pool
    global pool_index
    global is_spp_modeling
    global spp_loops
    global adj_pop_loops
    global pop_dis_coeff
    global all_solutions
    global best_solution
    global best_centersID
    global operators_selected
    global dev_move_counter
    global sls_move_possibility
    global tabuLength
    global tabuList
    global tabuSearch
    initialize_instance()
    district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
    #obj=location_model_lp(max_num_facility)
    #update_district_info()
    ###noprint "obj and facilities",obj,len(centersID),centersID
    if mip_solver not in mip_solvers: is_spp_modeling=-1
    myseed=seed
    if seed<0:
        myseed=random.randint(0,100)
    ##noprint "seed",myseed
    
    region_pool=[]
    all_solutions=[]
    t=time.time()
    best_biobjective = MAXNUMBER
    best_biobjective_global = MAXNUMBER
    best_biobjective = MAXNUMBER
    best_objective = MAXNUMBER
    best_objective_overload = MAXNUMBER
    last_loop_obj = MAXNUMBER
    pool_index=[[] for x in range(max_num_facility)]
    solutions=[]
    best_solution=[] 
    best_centersID=[]
    move_count=0
    deviation=intial_deviation
    last_deviation=deviation
    rule=acceptanceRule
    t_begin=time.time()
    t_h=time.time()
    #initial solutions as population
    if acceptanceRule in ["ils","vns","ilsvnd"]: #pop-based local search
        tabuSearch_current=tabuSearch
        tabuSearch=0
        multi_start=0
        for multi_start in range(multi_start_count):
            random.seed(myseed*100+multi_start)
            multi_start+=1
            t2=time.time()
            initial_solution(multi_start)
            #init_sol_model()
            if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)<1:
                ##noprint "check_solution_continuality_feasibility(node_groups)..."
                ##noprint node_groups
                return -1
            update_district_info()
            rule=acceptanceRule
            acceptanceRule=""
            RRT_local_search()
            RRT_local_search()
            update_region_pool_all()
            solutions.append([biobjective,centersID[:],node_groups[:],multi_start])
            acceptanceRule=rule
            arcpy.AddMessage("initial solution: "+str(biobjective))
            #population.append([biobjective,centersID[:],node_groups[:]]) 
            ##noprint "initial solution ", multi_start,":",int(biobjective),int(objective), int(objective_overload)
        solutions.sort(key=lambda x:x[0])
        all_solutions=solutions
        tabuSearch=tabuSearch_current
    #heuristic_time_limit=heuristic_time_limit-(time.time()-t_begin)
    not_improve=0
    not_improve_best=0
    adj_pop_loops=spp_loops
    if acceptanceRule=="mip":
        initial_solution(0)
        repare_fragmented_solution()
        update_district_info()
        RRT_local_search()
        mipmodel()
        update_district_info()
        update_best_solution()
        RRT_local_search()
        ##noprint "MIP results:",best_biobjective,best_objective,best_objective_overload
        is_spp_modeling=0
    if acceptanceRule=="vns":
        #for loop in range(SA_maxloops):
        tabuSearch=0
        loop=0
        not_improve_best=0
        if spp_loops<0: spp_loops=multi_start_count
        if adj_pop_loops<0: adj_pop_loops=multi_start_count
        while 1:
            loop+=1
            r=random.random()
            idx = int(min(multi_start_count,len(solutions))*r*r)
            node_groups=solutions[idx][2][:]
            update_district_info()
            #best_solution=node_groups[:]
            #best_biobjective=biobjective
            #update_best_solution()
            VNS_local_search()
            if best_biobjective_global+0.000000001 < solutions[0][0]: not_improve_best=0
            else: not_improve_best+=1
            ##noprint "pop:",[int(solutions[0][0]),int(solutions[min(multi_start_count,len(solutions))-1][0])],
            ##noprint acceptanceRule,loop,"bestg",int(best_biobjective_global*100)/100.0,int(best_overload_global),
            ###noprint "cbest", int(best_biobjective),int(best_objective),int(best_objective_overload),
            ##noprint "current", int(biobjective*100)/100.0,int(objective_overload),int((time.time()-t_h)*100)/100.0,not_improve_best
            solutions.append([biobjective,centersID[:],node_groups[:],loop])
            solutions.append([best_biobjective,centersID[:],best_solution[:],loop])
            solutions.append([best_biobjective_global,centersID[:],best_solution_global[:],loop])
            if not_improve_best%adj_pop_loops==adj_pop_loops-1:
                ##noprint "^",
                maxp=min(multi_start_count,len(solutions))
                if maxp%2==0: maxp-=1
                for i in range (maxp, 2,-2):  del solutions[i]
            if is_spp_modeling>1 and not_improve_best%spp_loops==spp_loops-1:
                ##noprint "*",
                if sppmodel()>=0:
                    update_district_info()
                    update_region_pool_all()
                    update_best_solution()
                    if biobjective<solutions[0][0]-0.0000001: not_improve_best=0
                    solutions.append([biobjective,centersID[:],node_groups[:],loop])
            solutions.sort(key=lambda x:x[0])
            solutions=selection(solutions)
            if time.time()-t_h > heuristic_time_limit: break
            arcpy.AddMessage(acceptanceRule +" loop "+str(loop) + " obj: " +str(best_biobjective_global))
    if acceptanceRule=="ilsvnd" or acceptanceRule=="ils":
        #for loop in range(SA_maxloops):
        tabuSearch=0
        not_improve_best=0
        if spp_loops<0:
            if acceptanceRule=="ilsvnd":  spp_loops=max(multi_start_count,20)
            else: spp_loops=max(50,multi_start_count*2)
            adj_pop_loops=spp_loops
        #if adj_pop_loops<0: adj_pop_loops=spp_loops
        loop=0
        while 1:
            loop+=1
            ##noprint acceptanceRule,"pop:",[int(solutions[0][0]),int(solutions[min(multi_start_count,len(solutions))-1][0])],
            move_count=0
            r=random.random()
            idx = int(min(multi_start_count,len(solutions))*r*r)
            #idx = random.randint(0,min(multi_start_count,len(solutions))-1)
            node_groups=solutions[idx][2][:]
            update_district_info()
            #best_solution=node_groups[:]
            #best_biobjective=biobjective
            #last_loop_obj=biobjective
            #last_loop_best=best_biobjective_global
            ruin_idx=random.randint(0,2)
            if ruin_idx==0:
                r_r_perb_location()
            if ruin_idx==2:
                r_r_perb_district()
            if ruin_idx==1:
                r_r_perb_mutation(0.005)
                #repare_fragmented_solution()
            update_best_solution()
            update_region_pool_all()
            ###noprint "R&R",ruin_idx, int(biobjective),int(objective),int(objective_overload),
                
            if acceptanceRule=="ilsvnd": VND_local_search()
            else: RRT_local_search()
            #update_best_solution()
            update_region_pool_all()
            if biobjective<solutions[0][0]-0.0000001: not_improve_best=0
            else: not_improve_best+=1
            solutions.append([biobjective,centersID[:],node_groups[:],loop])
            
            if not_improve_best%adj_pop_loops==adj_pop_loops-1:
                ##noprint "^",
                maxp=min(multi_start_count,len(solutions))
                if maxp%2==0: maxp-=1
                for i in range (maxp, 2,-2):  del solutions[i]
            if is_spp_modeling>1 and not_improve_best%spp_loops==spp_loops-1:
                ##noprint "*",
                if sppmodel()>=0:
                    update_district_info()
                    update_region_pool_all()
                    update_best_solution()
                    if biobjective<solutions[0][0]-0.0000001: not_improve_best=0
                    solutions.append([biobjective,centersID[:],node_groups[:],loop])
            solutions.sort(key=lambda x:x[0])
            solutions=selection(solutions)
            all_solutions=solutions
            t2=time.time()-t
            ##noprint acceptanceRule,loop,idx,"bestg",int(best_biobjective_global*100)/100.0,int(best_overload_global),
            ##noprint "current", int(biobjective*100)/100.0,int(objective_overload),move_count, int(t2*100)/100.0, not_improve_best
            if time.time()-t_h > heuristic_time_limit: break
            arcpy.AddMessage(acceptanceRule +" loop "+str(loop) + " obj: " +str(best_biobjective_global))
    if acceptanceRule=="hc" or acceptanceRule=="vnd" or acceptanceRule=="sls" or acceptanceRule=="rrt":
        best_biobjective_global = MAXNUMBER
        not_improve_best=0
        idx=0
        t_h=time.time()
        while 1:
            sls_t=time.time()
            random.seed(myseed*100+idx)
            idx+=1
            initial_solution(idx)
            update_district_info()
            update_region_pool_all()
            #repare_fragmented_solution()
            ##if spatial_contiguity==1  and check_solution_continuality_feasibility(node_groups)==0:
                ##noprint "check_solution_continuality_feasibility(node_groups)..."
            #update_district_info()
            update_best_solution()
            best_solution=node_groups[:]
            best_biobjective=biobjective
            best_objective=objective
            
            if acceptanceRule=="vnd":
                tabuSearch=0
                move_count=0
                VND_local_search()
                update_region_pool_all()
                #VND_local_search()
                #update_region_pool_all()
                ##noprint acceptanceRule,idx,"bestg",int(best_biobjective_global*100)/100.0,int(best_overload_global),
                ###noprint "cbest", int(best_biobjective),int(best_objective),int(best_objective_overload),
                ##noprint "current", int(biobjective*100)/100.0,int(objective_overload),move_count
                arcpy.AddMessage(acceptanceRule +" start "+str(idx) + " obj:" +str(best_biobjective_global))
                if time.time()-t_h >heuristic_time_limit: break
                continue
            if acceptanceRule=="hc":
                tabuSearch=0
                loop=0
                while 1:
                    loop+=1
                    move_count=0
                    last_loop_obj=biobjective
                    RRT_local_search()
                    update_region_pool_all()
                    ##noprint acceptanceRule,idx,loop,"bestg",int(best_biobjective_global),int(best_objective_global),int(best_overload_global),
                    ##noprint "cbest", int(best_biobjective),int(best_objective),int(best_objective_overload),
                    ##noprint "current", int(biobjective),int(objective),int(objective_overload),move_count
                    if abs(last_loop_obj-biobjective)<0.00000001: break
                    arcpy.AddMessage(acceptanceRule +" start "+str(idx) +" loop " +str(loop)+ " obj: " +str(best_biobjective_global))
                if time.time()-t_h >heuristic_time_limit: break
                continue
            if acceptanceRule=="sls" or acceptanceRule=="rrt":
                loop=0
                ar=acceptanceRule
                acceptanceRule=""
                RRT_local_search()
                acceptanceRule=ar
                sls_move_possibility=0.005
                deviation=intial_deviation
                #tabuLength=100
                tabuList=[]
                not_improved=0
                while 1:
                    loop+=1
                    move_count=0
                    dev_move_counter=0
                    last_best=best_biobjective
                    if loop%5==10:
                        node_groups=best_solution[:]
                        update_district_info()
                        #tabuList=[]
                        #tabuLength=num_districts
                    last_loop_obj=biobjective
                    RRT_local_search()
                    update_region_pool_all()
                    if acceptanceRule=="sls":
                        if dev_move_counter<1: sls_move_possibility *= 2
                        elif move_count<num_units/4: sls_move_possibility=sls_move_possibility*num_units/10/dev_move_counter
                        #else: sls_move_possibility=sls_move_possibility*max(num_districts,num_units/20)/dev_move_counter
                        else: sls_move_possibility=sls_move_possibility*move_count/dev_move_counter/10
                    rule=acceptanceRule
                    acceptanceRule=""
                    RRT_local_search()
                    acceptanceRule=rule
                    update_region_pool_all()

                    ##noprint acceptanceRule,idx,loop,"bestg",int(best_biobjective_global),int(best_objective_global),int(best_overload_global),
                    ##noprint "cbest", int(best_biobjective),int(best_objective),int(best_objective_overload),
                    ##noprint "current", int(biobjective),int(objective),int(objective_overload),move_count,dev_move_counter,
                    #if acceptanceRule=="sls":
                    #    ##noprint int(sls_move_possibility*10000)
                    #else: ##noprint deviation
                    arcpy.AddMessage(acceptanceRule +" start "+str(idx) +" loop " +str(loop)+ " obj: " +str(best_biobjective_global))
                    if best_biobjective < last_best: not_improved=0
                    else: not_improved+=1
                    if not_improved>10: break
                if time.time()-t_h >heuristic_time_limit: break
    if acceptanceRule=="sa":
        best_biobjective_global = MAXNUMBER
        idx=0
        t_h=time.time()
        while 1:        
            random.seed(myseed*100+idx)
            not_improve_best=0
            idx+=1
            initial_solution(idx)
            #repare_fragmented_solution()
            ##if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
                ##noprint "check_solution_continuality_feasibility(node_groups)..."
            update_district_info()
            update_best_solution()
            best_solution=node_groups[:]
            best_biobjective=biobjective
            best_objective=objective
            RRT_local_search()
            #tabuLength=100
            #tabuList=[]
            for loop in range (SA_maxloops):
                move_count=0
                if random.random()>0.5:
                    node_groups=best_solution[:]
                    update_district_info()
                    #update_best_solution()
                SA_coolingrate=math.exp( math.log(0.005)/SA_maxloops)
                SA_temperature=init_temperature*pow(SA_coolingrate,loop)
                last_loop_obj=biobjective
                RRT_local_search()
                update_region_pool_all()
                ##noprint acceptanceRule,idx,loop,"T=", int(SA_temperature*1000),"bestg",int(best_biobjective_global),int(best_objective_global),int(best_overload_global),
                ##noprint "cbest", int(best_biobjective),int(best_objective),int(best_objective_overload),
                ##noprint "current", int(biobjective),int(objective),int(objective_overload),move_count,int((time.time()-t_h)*1000)/1000.0
                arcpy.AddMessage(acceptanceRule +" start "+str(idx) +" loop " +str(loop)+ " obj: " +str(best_biobjective_global))
            if time.time()-t_h > heuristic_time_limit: break
                #if move_count==0: break
            #solutions[idx][0]=best_biobjective
            #solutions[idx][1]=centersID[:]
            #solutions[idx][2]=best_solution[:]

    ###noprint "bestg",int(best_biobjective_global),int(best_objective_global),int(best_overload_global),
    ###noprint "bestc",int(best_biobjective),int(best_objective),int(best_objective_overload)
    
    ##noprint "global best solution:",best_biobjective_global,best_objective_global,best_overload_global,time.time()-t
    node_groups=best_solution_global[:]
    update_district_info()
    update_best_solution()
    update_region_pool_all()
    if is_spp_modeling>=1 and acceptanceRule!="mip":
        if sppmodel()>=0:
            update_district_info()
            update_best_solution()
            ##noprint "spp solution:",best_biobjective_global,best_objective_global,best_overload_global,time.time()-t

    if spatial_contiguity==1  and check_solution_continuality_feasibility(best_solution_global)==0:
        ##noprint "infeasible final solution: continuality "
        return "infeasible solution on continuality"
    ##noprint "all time",time.time()-t
    ##noprint "time stat",time_op0,time_op1,time_op2,time_op3,time_op4    
    ##noprint "time_check,time_check_edge_unit,time_spp",time_check,time_check_edge_unit,time_spp
    ##noprint "move stat",count_op0,count_op1,count_op2,count_op3,count_op4
    ##noprint "check_count", check_count
    ##noprint best_biobjective_global, best_objective_global, best_overload_global, best_solution_global
    return [best_biobjective_global, best_objective_global, best_overload_global, best_solution_global]

def spp_mst_file(mip_mst_fn):
    feas_sol=[]
    num_pool=len(region_pool)
    for k in range(num_districts):
        ulist=[x for x in range(num_units) if best_solution_global[x]==k] #node_groups
        for i in range(num_pool):
            if ulist==region_pool[i][0]:
                feas_sol.append(i)
                break

    ##if len(feas_sol)<num_districts:
        ##noprint "len(sol)!=len(feas_sol) in spp mipstart"
        
##    f = open("sol.txt","w")
##    f.write("objective value: "+ str(biobjective)+"\n")
##    for i in range(len(feas_sol)):
##        f.write(str(i+1)+" "+ "X"+"{0:07d}".format(feas_sol[i])+ "  1\n")
##    f.flush()
##    f.close

    f = open(mip_mst_fn,"w")
    f.write('<?xml version = "1.0" encoding="UTF-8" standalone="yes"?>\n')
    f.write('<CPLEXSolutions version="1.2">\n')
    f.write(' <CPLEXSolution version="1.2">\n')
    f.write('  <header\n')
    f.write('    problemName=""\n')
    f.write('    solutionName="m0"\n')
    f.write('    solutionIndex="0"/>\n')
    f.write('  <variables>\n')
    idx=0
    for i in range(len(feas_sol)):
        s='   <variable name="' + "x_"+"{0:07d}".format(feas_sol[i])+'" index="'+str(idx) + '" value="1"/>\n'
        f.write(s)
        idx+=1
    f.write('  </variables>\n')
    f.write(' </CPLEXSolution>\n')
    f.write('</CPLEXSolutions>\n')
    f.flush()
    f.close()


def sppmodel():
    if mip_solver not in mip_solvers:
    #if mip_solver !="cplex" and mip_solver !="cbc":
        return
    global node_groups
    if len(region_pool)<=10:
        ##noprint "no candidate district!"
        return 0
    ###noprint "preparing data...total regions:",len(region_pool)
    alpha_coeff=avg_dis_min*pop_dis_coeff  
    prob = pulp.LpProblem("sdp_spp",pulp.LpMinimize)
    variables=[0 for x in range(len(region_pool))]
    costs=[0 for x in range(len(region_pool))]        
    ###noprint "buiding spp model..."
    for i in range(len(region_pool)):
        x=pulp.LpVariable("x_" +"{0:07d}".format(i), 0, 1,pulp.LpBinary)
        variables[i]=x
        costs[i]=region_pool[i][1]+region_pool[i][2]*alpha_coeff
        #costs[i]=region_pool[i][1]+region_pool[i][2]*100000000
        #objective+objective_overload*avg_dis_min*pop_dis_coeff
    obj=""
    for i in range(len(variables)):
        obj+=costs[i]*variables[i]
    prob+=obj

    for i in range(num_units):
        s=""
        for j in range(len(region_pool)):
            if i in region_pool[j][0]:
                s+=variables[j]
        prob+=s == 1

    #prob.writeLP("_spp.lp")
    mip_mst_file=''
    if mip_solver=='cplex':
        mip_mst_file=tempfile.mkstemp()[1]+"_mst.sol"
        spp_mst_file(mip_mst_file)
    else:
        mip_mst_file=tempfile.mkstemp()[1]+".txt"
        mips_start(mip_mst_file)
    cbc=pulp.solvers.COIN_CMD(maxSeconds=100,mip=1,msg=0,fracGap=0.00001,options=['vnd on', 'node hybrid', 'rens on','mips '+mip_mst_file])
    #if num_units>1000: cbc=pulp.solvers.COIN_CMD(maxSeconds=100,mip=1,msg=1,options=['vnd on', 'node hybrid', 'rens on'])
    ###noprint "Solving spp model..."
    if mip_solver=='cplex':
        cbc=pulp.solvers.CPLEX_CMD(msg=0,timelimit=100,options=['set threads 6','set mip tolerances mipgap 0.0000001', 'read '+mip_mst_file])
    cbc.actualSolve(prob)
    if prob.status<0:
       return prob.status #failer
    node_groups=[-1 for x in range(num_units)]
    for v in prob.variables():
        if (v.varValue >= 0.99):
            items=v.name.split('_')
            i=int(items[1])
            k=region_pool[i][3]
            for x in region_pool[i][0]:
                node_groups[x]=k
    update_district_info()
    return 1 #success
def mips_start(mipsfile):
    feas_sol=[]
    num_pool=len(region_pool)
    for k in range(num_districts):
        ulist=[x for x in range(num_units) if best_solution_global[x]==k] 
        for i in range(num_pool):
            if ulist==region_pool[i][0]:
                feas_sol.append(i)
                break

    #if len(feas_sol)<num_districts:
        ##noprint "len(sol)!=len(feas_sol) in spp mipstart"
        
    f = open(mipsfile,"w")
    f.write("objective value: "+ str(biobjective)+"\n")
    for i in range(len(feas_sol)):
        f.write(str(i+1)+" "+ "X"+"{0:07d}".format(feas_sol[i])+ "  1\n")
    f.flush()
    f.close
    return 1

        
def init_sol_model(rand):
    global node_groups
    prob = pulp.LpProblem("init_sdp",pulp.LpMinimize)
    variables={}
    costs={}
    alpha_coeff=avg_dis_min*pop_dis_coeff
    for i in range(num_units):
        for j in range(num_districts):
            variables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
            cost=nodedij[i][centersID[j]]*nodes[i][3]
            if rand==1:
                cost*=(random.random()+49.5)/50
            costs["x_" +str(i)+ "_"+ str(j)]=cost
##    tvariables={}
##    for i in range(num_districts):
##        tvariables["t_" +str(i)]=pulp.LpVariable("t_" +str(i), 0, None, pulp.LpInteger)

    obj=""
    for x in variables:
        obj += costs[x]*variables[x]
##    for x in tvariables:
##        obj += alpha_coeff*tvariables[x]
    prob +=obj
    for k in range(num_districts):
        s=variables["x_" +str(centersID[k])+ "_"+ str(k)]
        prob +=s == 1
    for i in range(num_units):
        s=""
        for j in range(num_districts):
            s+=variables["x_" +str(i)+ "_"+ str(j)]
        prob +=s == 1

    for k in range(num_districts):
        s=""
        for i in range(num_units):
            s+=nodes[i][3]*variables["x_" +str(i)+ "_"+ str(k)]
        #s-=tvariables["t_" +str(k)]
        prob+=s <= capacities[k]
    #prob.writeLP("_tp1.lp")
    cbc=pulp.solvers.COIN_CMD(mip=1,msg=0,maxSeconds=10,fracGap = 0.01)
    #prob.solve(solver=cbc)
    if mip_solver=="cplex":
        cbc=pulp.solvers.CPLEX_CMD(options=['set mip tolerances mipgap 0.003'])
        if rand==0:
            cbc=pulp.solvers.CPLEX_CMD(options=['set mip tolerances mipgap 0.001'])
    cbc.actualSolve(prob)

    if prob.status<0:
        ##noprint "model unsolved..."
        return -1
    sol=[]
    t=[]
    for v in prob.variables():
        if (v.varValue >= 0.90):
            ###noprint v,v.varValue
            items=v.name.split('_')
            i=int(items[1])
            if items[0]=='t':
                t.append([i,v.varValue])
                continue
            k=int(items[2])
            sol.append([i,k])
    node_groups=[-1 for x in range(num_units)]
    for i in range(len(sol)):
        node_groups[sol[i][0]]=sol[i][1]
    update_district_info()
    return pulp.value(prob.objective)


def init_sol_model2(rand):
    global node_groups
    prob = pulp.LpProblem("init_sdp",pulp.LpMinimize)
    variables={}
    costs={}
    alpha_coeff=avg_dis_min*pop_dis_coeff
    for i in range(num_units):
        for j in range(num_districts):
            variables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, None, pulp.LpInteger)
            cost=nodedij[i][centersID[j]] #*(random.random()+49.5)/50
            if rand==1:
                cost*=(random.random()+24.5)/25

            costs["x_" +str(i)+ "_"+ str(j)]=cost
##    tvariables={}
##    for i in range(num_districts):
##        tvariables["t_" +str(i)]=pulp.LpVariable("t_" +str(i), 0, None, pulp.LpInteger)

    obj=""
    for x in variables:
        obj += costs[x]*variables[x]
##    for x in tvariables:
##        obj += alpha_coeff*tvariables[x]
    prob +=obj
    for k in range(num_districts):
        s=variables["x_" +str(centersID[k])+ "_"+ str(k)]
        prob +=s == nodes[centersID[k]][3]
    for i in range(num_units):
        s=""
        for j in range(num_districts):
            s+=variables["x_" +str(i)+ "_"+ str(j)]
        prob +=s == nodes[i][3]

    for k in range(num_districts):
        s=""
        for i in range(num_units):
            s+=variables["x_" +str(i)+ "_"+ str(k)]
        #s-=tvariables["t_" +str(k)]
        prob+=s <= capacities[k]
    #prob.writeLP("_tp2.lp")
    cbc=pulp.solvers.COIN_CMD(mip=1,msg=0,maxSeconds=10,fracGap = 0.001)
    if mip_solver=="cplex":
        cbc=pulp.solvers.CPLEX_CMD(options=['set mip tolerances mipgap 0.000000001'])
    cbc.actualSolve(prob)

    if prob.status<0:
        ##noprint "model unsolved..."
        return -1
    sol=[[-1,-1] for x in range(num_units)]
    for v in prob.variables():
        if (v.varValue >= 0.90):
            ###noprint v,v.varValue
            items=v.name.split('_')
            if items[0]=="t":
                continue
            i=int(items[1])
            k=int(items[2])
            if v.varValue>sol[i][1]:
                sol[i][0]=k
                sol[i][1]=v.varValue
    node_groups=[x[0] for x in sol]
    update_district_info()
    return 

def mutation(rate):
    global node_groups
    ulist=find_edge_units()
    counter=0
    for uid in ulist:#(int(num_units*rate+0.5)):
        if counter>=rate*num_units: break
##        rid=node_groups[uid]
##        ulist2=[x for x in range(num_units) if node_groups[x]==rid and x!=uid]
##        if check_ulist_continuality(ulist2)==0: continue
        r=neighbor_regions(uid)
        if len(r)>=1 and node_groups[uid]!=r[0]:
            node_groups[uid]=r[0]
            counter+=1
    if spatial_contiguity==1: repare_fragmented_solution()
    #    else: repare_partial_solution()            

#mthd
#0 overlay A and B, delete fragements, repair by reassigning
#1\2\3 cover 70% of A on B,  delete fragements, repair by reassigning
#4 inject 30% of A into B
def cross(sol1,sol2,mthdod,crate):
    global node_groups
    node_groups=sol1[:]
    #ulist2=find_edge_units()
    #if random.random()<0.3:
    #    ##noprint 9,
    #    return
    mthd=mthdod
    if mthd==-1:
        mthd=random.randint(0,2)
    rate=1-crate #*random.random()
    #rate=0.1+(crate-0.1)*random.random()
    ulist=[x for x in range(num_units) if sol1[x]!=sol2[x]]

    #uniform random 
    if mthd==0: #insert each unit from sol2 to sol1 with possibility of rate
        for x in ulist:
            if random.random()<rate:
                ###noprint ",",
                node_groups[x]=sol2[x]
    #disturb some district
    if mthd==1: #insert each districts from sol2 to sol1 with possibility of rate
        rlist=range(num_districts)
        random.shuffle(rlist)
        rlist=rlist[0:int(num_districts*rate)]
        for x in ulist:
            if node_groups[x] in rlist:
                ###noprint ",",
                node_groups[x]=sol2[x]
    #disturb around some district
    if mthd==99:#insert districts 
        rlist=range(num_districts)
        random.shuffle(rlist)
        rlist=rlist[0:int(num_districts*rate)]
        for i in range(num_units):
            if sol2[i] in rlist:
                ###noprint ",",
                node_groups[i]=sol2[i]
    #meage splits
    if mthd==2:# districts
        sol12=[sol1[x]*1000+sol2[x] for x in range(num_units)]
        rlist=set(sol12)
        for r in rlist:
            ulist=[x for x in range(num_units) if sol12[x]==r]
            if random.random()<rate:
                k=r%1000
                for u in ulist: node_groups[u]=k
    if spatial_contiguity==1: repare_fragmented_solution()
    ##noprint mthd,
    return 

##def selectionnew(population):
##    population.sort(key=lambda x:x[0])
##    population2=[] #delete identical solution
##    population2.append(copy.deepcopy(population[0]))
##    ##noprint "similar?",
##    for x in population:
##        issimilar=0
##        ulist=[i for i in range(num_units) if x[2][i] != population2[-1][2][i]]
##        diffpop=sum(nodes[i][3] for i in ulist)*100.0/total_pop
##        diffunit=len(ulist)*100.0/num_units
##        if diffpop+diffunit<solution_similarity_limit:
##            issimilar=1
##        if issimilar==0:
##            population2.append(copy.deepcopy(x))
##        if len(population2)>=multi_start_count*2:
##            break
##    return population2

def selection(population):
    population1=copy.deepcopy(population)
    population1.sort(key=lambda x:x[0])
    population2=[] #delete identical solution
    population2.append(copy.deepcopy(population1[0]))
    selectidx=0
    for x in population1:
        issimilar=0
        for y in population2:
        #for k in [1]:
        #    y = population2[-1]
            ulist=[i for i in range(num_units) if x[2][i] != y[2][i]]
            diffpop=sum(nodes[i][3] for i in ulist)
            #if len(ulist)<min(num_units*1.0/num_districts,num_units/30.0) and diffpop*100.0/total_pop < min(3.0,100.0/num_districts): #100.0/num_districts: #<5%
            if len(ulist)<num_units*(solution_similarity_limit/100):
                issimilar=1
                break
        if issimilar==0:
            ###noprint selectidx,
            population2.append(copy.deepcopy(x))
        if len(population2)>=multi_start_count*2:
            break
        selectidx+=1
##    while len(population2) > multi_start_count:
##        idx=random.randint((multi_start_count+1)/2,len(population2)-1)
##        del population2[idx]
    return population2

def best_mutation_rate(stats1,stats2):
    cdiff=sum(x[0] for x in stats1) 
    mdiff=sum(x[0] for x in stats2)

    nsol=len(stats1)
    diffu=0
    diffpop=0
    for i in range(nsol-1):
        for j in range(i+1,nsol):
            ulist=[x for x in range(num_units) if stats1[i][-1][x] != stats1[j][-1][x]]
            diffu+=len(ulist)
            diffpop+=sum(nodes[x][3] for x in ulist)
    d1=0
    d2=0
    if nsol>2: d1=diffu  *200.0/nsol/(nsol-1)/num_units
    if nsol>2: d2=diffpop*200.0/nsol/(nsol-1)/total_pop

    nsol=len(stats2)
    diffu=0
    diffpop=0
    for i in range(nsol-1):
        for j in range(i+1,nsol):
            ulist=[x for x in range(num_units) if stats2[i][-1][x] != stats2[j][-1][x]]
            diffu+=len(ulist)
            diffpop+=sum(nodes[x][3] for x in ulist)
    d3=diffu  *200.0/nsol/(nsol-1)/num_units
    d4=diffpop*200.0/nsol/(nsol-1)/total_pop

    ##noprint "diff of new solutions:",[d1,d2],[d3,d4],cdiff,mdiff
    return max(d1,d2),max(d3,d4),cdiff,mdiff

def solver_time_limit_set(t):
    global heuristic_time_limit
    heuristic_time_limit=t
    
    
def initial_solution(idx):
    global node_groups
    global initial_solution_method
    if mip_solver not in mip_solvers: initial_solution_method=[2]
    num=len(initial_solution_method)
    method=idx%num
    #method=initial_solution_method[midx]
    ###noprint idx,
    node_groups=[-1 for x in range(num_units)]
    if initial_solution_method[method] ==2:
        for k in range(num_districts):
            node_groups[centersID[k]]=k
        ###noprint idx,"2rgowth",
        repare_partial_solution()
    if initial_solution_method[method] ==1:
        ###noprint idx, "1binmodel",
        init_sol_model(1)
        if spatial_contiguity==1: repare_fragmented_solution()
    if initial_solution_method[method] ==0:
        ###noprint idx,"0intmodel",
        init_sol_model2(1)
        if spatial_contiguity==1: repare_fragmented_solution()

    
def ga(numf,m,timelimit,mthd,crate, mrate,spp,myseed):
    global multi_start_count
    global seed
    global acceptanceRule
    global best_objective
    global best_biobjective
    global best_objective_overload
    global best_biobjective_global
    global objective
    global biobjective
    global objective_overload
    global node_groups
    global centersID
    global district_info
    #global node_neighbors
    global move_count
    global region_pool
    global pool_index
    global is_spp_modeling
    global spp_loops
    global adj_pop_loops
    #global pop_dis_coeff
    global all_solutions
    global operators_selected
    global max_num_facility
    global heuristic_time_limit
    global adjust_mutation_rate
    initialize_instance()
    if m<2: 
        ##noprint "the number of facilities must be greater than 1."	
        return
    cur_crate=crate
    cur_mrate=mrate
    heuristic_time_limit=timelimit
    mutation_rate_adjustmented=int(mrate*num_units) #param
    #evolution_stats=[]
    max_num_facility=numf
    acceptanceRule='ga'
    is_spp_modeling=spp
    if mip_solver not in mip_solvers: is_spp_modeling=-1
    all_solutions=[]
    multi_start_count=m
    seed=myseed
    if seed<0:
        seed=random.randint(0,100)
    random.seed(seed)
    ##noprint "seed",seed
    region_pool=[]
    t=time.time()
    ga_time=0.0
    best_biobjective_global = MAXNUMBER
    best_biobjective = MAXNUMBER
    district_info = [[0,0.0,0,0,0] for x in range(num_districts)]

    population=[] #all
    pool_index=[[] for x in range(numf)]
    lp_obj=avg_dis_min*total_pop
    optimum=99.99
    t_ga=time.time()
    multi_start=0
    while 1: #multi_start<multi_start_count:
        random.seed(seed+multi_start*100)
        t2=time.time()
##        if multi_start==1 and (mip_solver in mip_solvers):
##            ##noprint str(multi_start)+"*",
##            lp_obj=init_sol_model(0)
##            repare_fragmented_solution()
##        else:
##            ##noprint multi_start,
##            initial_solution(multi_start)
        initial_solution(multi_start)
        multi_start+=1
        RRT_local_search()
        RRT_local_search()
        update_best_solution()
        update_region_pool_all()
        if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
            ##noprint "check_solution_continuality_feasibility(node_groups)..."
            ##noprint node_groups
            return
        for k in range(num_districts):
            if node_groups[centersID[k]]!=k:
                ##noprint "check the center unit ...",k,centersID[k],node_groups[centersID[k]]
                return
        population.append([biobjective,centersID[:],node_groups[:],chr(97+multi_start)])
        opt=(biobjective-lp_obj)/lp_obj #compare with lower bound (no contiguity, no unit integrity)
        if opt<optimum: optimum=opt
        ##noprint "initial solution",biobjective,objective, objective_overload,int((time.time()-t2)*100)/100.0, int(opt*10000)/10000.0
        arcpy.AddMessage("initial solution "+str(multi_start) +": " +str( biobjective))
        if len(population)>= multi_start_count:
            break
    population.sort(key=lambda x:x[0])
    ##noprint "best init solution, and optimality",population[0][0],int((time.time()-t_ga)*100)/100.0,optimum
    stats=[]
    evolution_c_stats=[]
    evolution_m_stats=[]
    stats_mutation=[]
    ##noprint "lower_bound on obj:",lp_obj
    #t_ga=time.time()
    not_improved=0
    improved_time=time.time()
    #ulist=find_edge_units()
    if spp_loops<0: #auto set
        if 2 in operators_selected:
            spp_loops=max(multi_start_count*2,40) #multi_start_count*multi_start_count
            adj_pop_loops=multi_start_count*2
        elif 1 in operators_selected:
            spp_loops=multi_start_count*multi_start_count
            adj_pop_loops=multi_start_count*multi_start_count
        else:
           spp_loops=multi_start_count*multi_start_count*5
           adj_pop_loops=multi_start_count*multi_start_count*5
        adj_pop_loops=spp_loops
    loop=0
    while 1:
        #loop+=1
        if time.time()-t_ga > heuristic_time_limit:  break
        #step1: selection
        #idx2=random.randint(0,min(multi_start_count,len(population))-1)
        #idx1=selection_solution(min(multi_start_count/2,len(population)/2))
        r=random.random()
        idx1 = int(min(multi_start_count/2,len(population))* pow(r,1))
        r=random.random()
        idx2 = int(min(multi_start_count,len(population)) * pow(r,1))
        if idx1==idx2: continue
        loop+=1
        b1=int(population[0][0])
        i=min(len(population),multi_start_count)-1
        b2=int(population[i][0])
        diff1,diff2=pop_diff(population)
        ##noprint [b1,b2,len(population)], [diff1,diff2],
        ##noprint "gen", loop,idx1,idx2,
        ###noprint [int(cur_crate*1000)/1000.0,int(cur_mrate*1000)/1000.0],
        sol1=population[idx1][2]
        sol2=population[idx2][2]
        diffunits=0
        optimum=(population[0][0]-lp_obj)/lp_obj
        p_obj=population[idx1][0]
        #step2: crossover
        cur_mrate=(1+random.random())*mrate/2
        if random.random()<0.3 or mthd==9:
            ##noprint 9,
            node_groups=sol1[:]
            update_district_info()
        else:
            cur_crate=0.5		
            if diff1>=1: cur_crate=1-mrate/diff1*100
            if cur_crate<0.5:cur_crate=0.5
            if cur_crate>crate:cur_crate=crate
            cross(sol1,sol2,mthd,cur_crate)
            ulist=[x for x in range(num_units) if sol1[x]!=node_groups[x]]
            diffunits=len(ulist)
            update_best_solution()
            update_region_pool_all()
        
        #step2b: local search
        RRT_local_search()
        update_region_pool_all()
        population.append([biobjective,centersID[:],node_groups[:]])
        sign ="+"
        if biobjective+0.00000001 < p_obj: sign="-"
        if biobjective < population[0][0]:
            sign="*"
            #RRT_local_search()
            #update_region_pool_all()
            not_improved=0
            improved_time=time.time()
        ##noprint sign,
        evolution_c_stats.append([diffunits,
                            biobjective,
                            population[idx1][0],
                            node_groups[:]
                           ])

        #step3: mutation
        p_obj=biobjective
        cur_mrate=(1+random.random())*mrate/2
        diffunits2=0
        sol_c=node_groups[:]
        mutation(cur_mrate)
        ulist=[x for x in range(num_units) if sol_c[x]!=node_groups[x]]
        diffunits2=len(ulist)
        update_district_info()
        update_best_solution()
        update_region_pool_all()
        #step4b: local search                    
        RRT_local_search()
        update_region_pool_all()
        sign ="+"
        if biobjective+0.0000001 < p_obj: sign="-"
        if biobjective +0.00000001 >= population[0][0]:
            not_improved+=1
        else:
            not_improved=0
            improved_time=time.time()
            #RRT_local_search()
            #update_region_pool_all()
            sign="*"
        ##noprint sign,
        evolution_m_stats.append([diffunits2,
                                cur_mrate,
                                biobjective,
                                population[idx1][0],
                                node_groups[:]
                               ])
        stats.append([loop,diffunits,diffunits2,p_obj-biobjective,(biobjective-best_biobjective_global)/best_biobjective_global])
        population.append([biobjective,centersID[:],node_groups[:]])
        ##noprint int(diffunits),diffunits2,
        ##noprint "cur", int(biobjective*100)/100.0,int(objective_overload),"best",int(best_biobjective_global*100)/100.0, 

        #local optimum: renew the population, and reselection by spp modeling 
#        if is_spp_modeling==1 and loop%spp_loops==spp_loops-1:
        
        if (not_improved%adj_pop_loops==adj_pop_loops-1) and multi_start_count>5 and len(population)>5:
            #maxp=min(multi_start_count,len(population))
            #if maxp%2==0: maxp-=1
            #for i in range (maxp, 2,-2):
            #    del population[i]
            psize=min(len(population)/3,multi_start_count/3)
            for i in range (psize):
                idx=random.randint(1,min(multi_start_count,len(population)))
                del population[idx]
            ##noprint "^",

        #if is_spp_modeling>1 and (not_improved%spp_loops==spp_loops-1 and time.time()-improved_time>heuristic_time_limit/20):
        #if is_spp_modeling>1 and time.time()-improved_time>heuristic_time_limit/20:
        if is_spp_modeling>1 and not_improved%spp_loops==spp_loops-1:
            ##noprint "*",
            sppmodel()
            update_district_info()
            update_best_solution()
            update_region_pool_all()
            RRT_local_search()
            update_region_pool_all()
            improved_time=time.time()
            if biobjective+0.00000001 < population[0][0]:
                not_improved=0
            population.append([biobjective,centersID[:],node_groups[:]])

        #step4 update population
        population.sort(key=lambda x:x[0])
        population2=selection(population)
        if len(population2) >=multi_start_count/2 and len(population2)>=2:
            population=population2
        while len(population)>multi_start_count*2:
            population.pop()
        ##noprint not_improved,int((time.time()-t_ga)*100)/100.0
        arcpy.AddMessage("loop "+str(loop) +": " +str( best_biobjective_global))

    population.sort(key=lambda x:x[0])
    node_groups=best_solution_global[:] #population[0][2][:]
    update_district_info()
    ##noprint "all solutions:"
    #for x in  all_solutions:
    #    ##noprint x[0:-1]
    ga_time=time.time()-t_ga
    ##noprint "global best solution:",biobjective,objective,objective_overload,ga_time
    t_spp=time.time()
    if is_spp_modeling>=1:
        sppmodel()
        update_district_info()
        update_best_solution()
        ##noprint "number of areas recorded", len(region_pool)
        ##noprint "spp solution:",biobjective,objective,objective_overload,time.time()-t_spp, time.time()-t
    RRT_local_search()
    ##noprint "final LS solution:",biobjective,objective,objective_overload
    
    if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
        ##noprint "infeasible final solution: continuality "
        return "infeasible final solution: continuality"
    ##noprint "time",time.time()-t
    #for x in stats: ##noprint x
    #diff1=sum([x[1] for x in stats])*1.0/len(stats)
    #diff2=sum([x[2] for x in stats])*1.0/len(stats)

    ##noprint "op time",time_op0,time_op1,time_op2,time_op3,time_op4
    ##noprint "op moves",count_op0,count_op1,count_op2,count_op3,count_op4
    ##noprint "time_check,time_check_edge_unit,time_spp",time_check,time_check_edge_unit,time_spp
    ##noprint "check_count",check_count
    ##noprint "not_improved loops",not_improved
    ##noprint "DistrictId, No.units, pop, cap, dis"
    #for i in range(num_districts):
        ##noprint i,district_info[i][0],district_info[i][1],district_info[i][3], int(district_info[i][2]*100)/100
    #return best_biobjective_global,best_objective_global,objective_overload, node_groups
    return [best_biobjective_global,best_objective_global,best_overload_global ,best_solution_global]
def selection_solution(n):
    r=random.randint(1,n*(n+1)/2)
    idx=-1
    for i in range(n):
        r-= n-i
        if r<=0:
            idx=i
            break
    return idx
        
def pop_diff(population):
    diff1=0 #units
    diff2=0 #pop
    psize=min(multi_start_count,len(population))
    if psize<=1: return 0,0
        
    #len(population)
    for i in range(psize-1):
        for j in range(i+1,psize):
            ulist=[x for x in range(num_units) if population[i][2][x] != population[j][2][x]]
            diff1+=len(ulist)
            diff2+=sum(nodes[x][3] for x in ulist)
    return int(diff1*2000.0/psize/(psize-1)/num_units)/10.0, int(diff2*2000.0/psize/(psize-1)/total_pop)/10.0, #percentage

def non_near_list(nnn):
    nlist=[]
    #return nlist
    n=nnn
    if n>12: n=12
    if n<6: n=6
    for i in range(num_units):
        fdlist=[]
        for k in range(len(centersID)):
            fdlist.append([nodedij[i][centersID[k]],k])
        fdlist.sort(key=lambda x:x[0])
        for j in range(n,num_districts):
            nlist.append([i,fdlist[j][1]])
    return nlist



