# Delineating service areas
The design of service areas is one of the essential issues in providing efficient services in both the public and private sectors. For a geographic area with basic areal units, the SAP should assign the service-demand areal units to service-supply units such that each facility has a service area and some criteria are satisfied. The basic criteria for the problem include the balance of service demand and supply, the highest service accessibility, the contiguity of service areas, and the integrity of basic units. The balance criterion means that the total service demand in each area should be no greater than its service capacity. Service accessibility can be evaluated by total travel distance from demand units to their supply units. The shortest travel distance is usually preferred when using the service. Contiguous service area is also a necessity for satisfying policy or management purposes. In service area design practice, splitting a demand unit is usually not allowed.

# ArcGIS tool for delineating service areas
We have designed the tool in ArcGIS for delineating service areas. Various algorithms are surpported:
1. Local-search based metaheuristics such as ILS, VNS, SA, RRT, SLS, VND, HC;
2. Population based metaheuristics GA;

# How to use the tool
Install the software:
1. PuLP 1.6.0 (https://pypi.org/project/PuLP/) (optional but recommended);
2. ILOG CPLEX 12.x and CPLEX Python API (optional).
3. Copy all the files to a file directory. 
4. In ArcGIS, nevigate to the file directory, click the tool. 
# E-mail: yfkong@henu.edu.cn
