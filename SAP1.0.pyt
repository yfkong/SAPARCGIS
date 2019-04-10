# -*- coding: utf-8 -*-
import arcpy, os
import saparcgis as d

class Toolbox(object):
    def __init__(self):
        """Define the toolbox (the name of the toolbox is the name of the   .pyt file)."""
        self.label = "SAP Toolbox"
        self.alias = "Districting for facilities"
        # List of tool classes associated with this toolbox
        self.tools = [Tool]

class Tool(object):
    def __init__(self):
        """Define the tool (tool name is the name of the class)."""
        self.label = "Delineating service areas for facilities"
        self.description = "Delineating service areas for facilities"
        self.canRunInBackground = False

    def getParameterInfo(self):
        """Define parameter definitions"""
        feas=arcpy.Parameter(name='feas', displayName='Map layer', datatype='GPFeatureLayer', direction='Input',parameterType='Required')
        fld_id=arcpy.Parameter(name='id_fld', displayName='ID filed', datatype='Field', direction='Input', parameterType='Required')
        fld_id.parameterDependencies = [feas.name]
        fld_demand=arcpy.Parameter(name='demand_fld', displayName='Demand filed', datatype='Field', direction='Input', parameterType='Required')
        fld_demand.parameterDependencies = [feas.name]
        fld_supply=arcpy.Parameter(name='supply_fld', displayName='Supply filed', datatype='Field', direction='Input', parameterType='Required')
        fld_supply.parameterDependencies = [feas.name]
        connectivity=arcpy.Parameter(name='connectivity', displayName='connectivity?', datatype='GPBoolean',direction='Input',parameterType='Optional')
        connectivity.value=True
        #solver,popsize,timelimit,spp
        solver=arcpy.Parameter(displayName="Solver", name="Solver", datatype="GPString",parameterType="Required", direction="Input")
        solver.filter.type = 'ValueList'
        solver.filter.list = ['ga','ils','vns','ilsvnd','hc','sa','rrt','sls','mip']

        popsize=arcpy.Parameter(displayName="Pop size/Multistarts", name="popsize", datatype="GPLong",parameterType="Required", direction="Input")
        popsize.value=10
        timelimit=arcpy.Parameter(displayName="Time limit in seconds", name="timelimit", datatype="GPLong",parameterType="Required", direction="Input")
        timelimit.value=300
        spp=arcpy.Parameter(displayName="SPP modeling (0,1,2)", name="spp", datatype="GPLong",parameterType="Required", direction="Input")
        spp.value=1
        
        mip_solver=arcpy.Parameter(displayName="MIP Solver", name="mipSolver", datatype="GPString",parameterType="Required", direction="Input")
        mip_solver.filter.type = 'ValueList'
        slist=d.mip_solvers[:]
        slist.append("_")
        mip_solver.filter.list = slist
        mip_solver.value=slist[0]		
        outfile=arcpy.Parameter(name='outfile', displayName='Output layer', datatype='DEFeatureClass', direction='Output',parameterType='Required')
        operator=arcpy.Parameter(displayName="operator", name="Search operators", datatype="GPString",parameterType="Required", direction="Input")
        operator.filter.type = 'ValueList'
        operator.filter.list = ['one-unit-move','two-unit-move','three-unit-move']		
        operator.value='two-unit-move'
        return [feas,fld_id,fld_demand, fld_supply, outfile,connectivity,solver,popsize,timelimit,spp,mip_solver,operator]

    def isLicensed(self):
        """Set whether tool is licensed to execute."""
        return True

    def updateParameters(self, parameters):
        """Modify the values and properties of parameters before internal
        validation is performed.  This method is called whenever a parameter
        has been changed."""
        return

    def updateMessages(self, parameters):
        """Modify the messages created by internal validation for each tool
        parameter.  This method is called after internal validation."""
        return

    def execute(self, parameters, messages):
        """The source code of the tool."""
        if arcpy.env.workspace==None:
             arcpy.AddMessage("please set the workspace! 'Geoprocessing'->'Envronments.'")		
             return
        arcpy.AddMessage("available MIP solvers "+str(d.mip_solvers) )		
        dataTable=[]
        fn=parameters[0].value
        desc = arcpy.Describe(fn)
        idf=parameters[1].valueAsText
        df=parameters[2].valueAsText
        sf=parameters[3].valueAsText
        arcpy.AddMessage("reading spatial units ...")
        cursor = arcpy.SearchCursor(parameters[0].value)
        row = cursor.next()
        idx=0
        fcenters=[]
        capacities=[]
        id2idx={}
        while row:
            x=0
            y=0
            r=[idx,x,y,row.getValue(df),row.getValue(idf),row.getValue(sf),0,0]
            if r[5]>0: 
                fcenters.append(idx)
                capacities.append(r[5])
            dataTable.append(r)
            row = cursor.next()
            id2idx[r[4]]=r[0]
            idx+=1
        del cursor, row
        d.nodes=dataTable
        num_units=len(dataTable)
        arcpy.env.overwriteOutput = True

        geometries = arcpy.CopyFeatures_management(fn, arcpy.Geometry())			
        for i in range(num_units):
            cid=geometries[i].centroid
            dataTable[i][1]=cid.X
            dataTable[i][2]=cid.Y
            #arcpy.AddMessage("units: "+str(dataTable[i]))
        arcpy.AddMessage("total units: "+str(num_units))
        arcpy.AddMessage("total spply units: "+str(len(fcenters)) )

        #connectivity
        ws=arcpy.env.workspace
        if ws.find(".gdb"):
            ws=os.path.dirname(arcpy.env.workspace)
            arcpy.env.workspace=ws
        arcpy.AddMessage("searching for neighbor units ... " )
        swm="swm.swm"
        swmdb="swm.dbf"
        if arcpy.Exists(swm): arcpy.Delete_management(swm)
        if arcpy.Exists(swmdb): arcpy.Delete_management(swmdb)
        if desc.shapeType=='Point':
            arcpy.GenerateSpatialWeightsMatrix_stats (fn, idf, swm,"DELAUNAY_TRIANGULATION" )
        else:
            arcpy.GenerateSpatialWeightsMatrix_stats (fn, idf, swm, "CONTIGUITY_EDGES_ONLY")
        arcpy.ConvertSpatialWeightsMatrixtoTable_stats(swm, swmdb)
        unit_neighbors=[[] for x in range(num_units) ] 
        rows = arcpy.SearchCursor(swmdb)
        for row in rows:
            id1=row.getValue(idf)
            id2=row.getValue("NID")
            unit_neighbors[id2idx[id1]].append(id2idx[id2])
        del row, rows
        #for x in unit_neighbors:  arcpy.AddMessage(str(x))
        arcpy.AddMessage("calcaulating distance ... " )
        dist_ij=[[999999.999 for x in range(num_units) ] for y in range(num_units)]
        for i in range(num_units):
            for j in range(i,num_units):
                if j==i: 
                    dist_ij[i][j]=0.0
                    continue
                d2=pow(dataTable[i][1]-dataTable[j][1],2)
                d2+=pow(dataTable[i][2]-dataTable[j][2],2)
                d3=pow(d2,0.5)/1000
                dist_ij[i][j]=d3
                dist_ij[j][i]=d3
        d.nodes=dataTable
        d.centersID=fcenters
        d.capacities=capacities
        d.node_neighbors=unit_neighbors
        d.nodedij=dist_ij
        d.num_districts=len(fcenters)
        sol=[0 for x in range(num_units)]
        if d.check_continuality_feasibility(sol,0)==0:
            arcpy.AddMessage("the spatial units are not connected!")
            return
        #d.initialize_instance()
        #arcpy.AddMessage("facilities: "+str(d.centersID) )
        #arcpy.AddMessage("capacities: "+str(d.capacities) )
        #arcpy.AddMessage("distance: "+str(dist_ij) )
        #d.readfile("..\zys_13a.txt", "..\zys_connectivity.txt")
        #biobj,obj,overload,sol=d.ga(13,5, 100, -1, 0.7, 0.03, 1,-1)		
        
        d.spatial_contiguity=1
        if parameters[5].value==False:  d.spatial_contiguity=0
        solver=parameters[6].valueAsText
        psize=parameters[7].value
        timelimit=parameters[8].value
        spp=parameters[9].value
        d.mip_solver=parameters[10].valueAsText
        if d.mip_solver not in d.mip_solvers:
            spp=0
        operator=parameters[11].value
        if operator=='one-unit-move': d.operators_selected=[0] 
        if operator=='two-unit-move':d.operators_selected=[0,1] 
        if operator=='three-unit-move': d.operators_selected=[0,1,2] 

        #d.initial_solution_method=[1]
        #d.SA_maxloops = 100
        #d.init_temperature=1.0
        #d.spp_loops=50
        #d.intial_deviation=0.5		
        #d.operators_selected=[0,1] 
        arcpy.AddMessage("solving the problem......")	
        arcpy.SetProgressorLabel("solving the problem......")		
        if solver=='ga':
            results=d.ga(d.num_districts, psize, timelimit, -1, 0.7, 0.03, spp,-1)
        else:
            d.set_solver_params(d.num_districts,solver,psize, timelimit, spp, -1)
            results=d.solve()
        if len(results)<=1:	
            arcpy.AddMessage("Fatal solver error!!!")		
            if len(results)==1: arcpy.AddMessage(str(results[0]))	
            return
        biobj=results[0]
        obj=results[1]
        overload=results[2]
        sol=results[3]
        arcpy.SetProgressorLabel("outputting the service area layer ...")
        arcpy.AddMessage("obj, total distance and overload: " + str(biobj)+" "+str(obj) + " "+str(overload))
        #arcpy.AddMessage("solution: " +str(sol))
        arcpy.env.overwriteOutput = True
        newlayer=arcpy.CopyFeatures_management(parameters[0].value, parameters[4].value)
        arcpy.AddField_management(newlayer, "SA_ID", "Long")
        cursor = arcpy.UpdateCursor(newlayer)
        row = cursor.next()
        idx=0
        while row:
            row.setValue("SA_ID", sol[idx])
            cursor.updateRow(row)
            row = cursor.next()
            idx+=1
        del cursor, row		
        arcpy.AddMessage("solution summary...")
        arcpy.AddMessage("obj, total distance and overload: " + str(biobj)+" "+str(obj) + " "+str(overload))
        arcpy.AddMessage("ServiceAreaId, FacilityID, No.units, total demand, supply, total distance")
        for i in range(d.num_districts):
            arcpy.AddMessage("{0},{1},{2},{3},{4},{5}".format(i,dataTable[d.centersID[i]][4],d.district_info[i][0],d.district_info[i][1],d.district_info[i][3], int(d.district_info[i][2]*1000)/1000.0))
        return
