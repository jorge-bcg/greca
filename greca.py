import streamlit as st
import pandas as pd
import os
import numpy as np
from openrouteservice import Client
from geopy.distance import geodesic
import requests
import json
import networkx as nx
import geopandas as gpd
import shapely
from shapely.geometry import Point, box
from shapely.ops import transform
#from shapely import Point
import pyproj
import math
from google.cloud import secretmanager
#import google-cloud-secret-manager as gsm

ors_url = "https://api.openrouteservice.org/v2/matrix/driving-car"
GC_API_URL = "https://api.goclimateneutral.org/v1/flight_footprint"

#Make sure to run the following in the GCloud LI: gcloud auth application-default login
project_id = "greca-418615"
client = secretmanager.SecretManagerServiceClient()
name = f"projects/{project_id}/secrets/GC_API_KEY/versions/1"
response = client.access_secret_version(name=name)
GC_API_KEY = response.payload.data.decode("UTF-8")

# print(GC_API_KEY)

#First cut filtering by using a bounding box
def filterCities(sel,a, buffer):
	x_buff = (sel['lon'].max() - sel['lon'].min())*buffer/100
	y_buff = (sel['lat'].max() - sel['lat'].min())*buffer/100 
	bx1, bx2 = [sel['lon'].min() - x_buff, sel['lon'].max() + x_buff]
	by1, by2 = [sel['lat'].min() - y_buff, sel['lat'].max() + y_buff]
	filtered = a.loc[(a['lon']>=bx1) & (a['lon'] < bx2) & (a['lat'] >= by1) & (a['lat'] < by2)]
	return filtered

#This provides a first ranking of cities based on proximity and distance traveled
def rankCities(sel,p):

	city_pairs = pd.DataFrame(columns=['origin_id','origin_name', 'origin_pop','attendees','destination_id','destination_name','destination_pop'])
	for s in range(len(sel)):
		cpd = {"origin_id": [(sel.iloc[s]['id'])] * len(p), "origin_name": [(sel.iloc[s]['Name'])] * len(p), "origin_pop": [(sel.iloc[s]['Population'])] * len(p) , \
		 "attendees": [(sel.iloc[s]['Number of attendees'])] * len(p), "destination_id": p['id'].to_list(), "destination_name": p['Name'].to_list(), "destination_pop": p['Population'].to_list() }
		cp = pd.DataFrame(cpd)
		city_pairs = pd.concat([city_pairs, cp])
	city_pairs = pd.merge(city_pairs,distances, how="left", on=["origin_id","destination_id"])

	city_pairs['gravity_score'] = (city_pairs['origin_pop'] * city_pairs['destination_pop']) / (city_pairs['distance'].clip(lower=10)** 2) / 1000000

	city_pairs['PMT'] = city_pairs['attendees'] * city_pairs['distance']

	# Group by the 'category' column
	top_cities_gb = city_pairs.groupby('destination_id')

	# Apply aggregation functions to the grouped data
	top_cities = top_cities_gb.agg(
		PMT_sum=pd.NamedAgg(column="PMT", aggfunc="sum"),
		GS_sum=pd.NamedAgg(column="gravity_score", aggfunc="sum")
	)

	top_cities = pd.merge(top_cities,cities,left_on="destination_id", right_on="id")
	top_cities['gravity_score_pctile'] = top_cities['GS_sum'].rank(pct=True, ascending=True) #The strongest potential is in higher gravity scores
	top_cities['PMT_pctile'] = top_cities['PMT_sum'].rank(pct=True, ascending=False) #The strongest potential is in lower PMT
	top_cities['comb_score'] = ((top_cities['gravity_score_pctile']*pop_weight)+(top_cities['PMT_pctile']*(100-pop_weight)))/100
	top_cities.sort_values(by='comb_score', ascending=False, inplace=True)
	top_cities['rank'] = top_cities['comb_score'].rank(ascending=False) #The strongest potential is in higher scores
	top_cities = top_cities[(top_cities['comb_score']>=(1-first_filter_top_pctile)) & (top_cities['rank'] <= 50)] #Max of 50 cities due to API limitations
	cols = top_cities.columns.to_list()	
	cols = cols[-1:] + cols[:-1]
	top_cities = top_cities[cols]

	return top_cities

#Quick function for projecting the lat-lon
def projectPoint(p): 
	wgs84_pt = p

	wgs84 = pyproj.CRS('EPSG:4326')
	wgs84_epsg = pyproj.CRS('EPSG:3857')

	project = pyproj.Transformer.from_crs(wgs84, wgs84_epsg, always_xy=True).transform
	proj_point = transform(project, wgs84_pt)
	return proj_point

#Selecting the route chosen for flying 
def selectAirPath(array):
	if len(array) == 0 or (array[0] is None):
		return []
	else: #Just going by the one with fewest stops (that's what I'd do)
		sorted_array = sorted(array, key=lambda x: len(x[0]), reverse=False)
	return sorted_array[0]

def adjustAirPath(array):
	#This will take the OD air path array and adjust it for inclusion in the output dataframe
	formatted_routes = []
	adjusted_distances = []
	adjusted_flight_times = []

	for i in array: #There should be one element per selected city
		if len(i) == 0: #There was no good route
			formatted_routes.append(None)
			adjusted_distances.append(None)
			adjusted_flight_times.append(None)
		else:
			formatted_routes.append("-".join(i[0]))
			adjusted_distances.append(i[1]+i[2]) #Summing the air + airport acc/egg distance
			aft = layover_duration*(len(i[0])-2) + (i[2]/airport_access_driving_speed) + airport_access_security + i[3]
			adjusted_flight_times.append(aft)
	return [formatted_routes,adjusted_distances,adjusted_flight_times]

def computeFlightMetrics(sel,p):
	
	routes = []
	pmt = []
	pht = []

	for pc in range(len(p)):

		prog_bar.progress(pc/len(p), text="Working on the analysis...")
		destination = Point(p.iloc[pc]['lon'],p.iloc[pc]['lat'])
		de_xy = (p.iloc[pc]['lat'],p.iloc[pc]['lon'])
		destination_pj = projectPoint(destination)
		destination_bf = shapely.buffer(destination_pj,distance=(50*1609))
		nearest_dest_airports = airports.sindex.query(destination_bf, predicate="intersects")
		air_trips = [[]* 4] * len(sel) #Storing the results in this 2D array, one subarray for each of the origin cities
		
		for s in range(len(sel)):
			flight_options = []
			if len(nearest_dest_airports) == 0:
				#No commercial airports within the desired distance
				continue
			
			if p.iloc[pc]['Name'] == sel.iloc[s]['Name']: #If it's the same city
				continue
			
			origin = Point(sel.iloc[s]['lon'],sel.iloc[s]['lat'])
			og_xy = (sel.iloc[s]['lat'],sel.iloc[s]['lon'])
			origin_pj = projectPoint(origin)
			origin_bf = shapely.buffer(origin_pj,distance=(50*1609))
			
			if (geodesic(og_xy, de_xy).m /1609 < min_flight_distance): #If too short to fly
				continue

			nearest_airports = airports.sindex.query(origin_bf, predicate="intersects")
			if len(nearest_airports) == 0:
				continue
			else:
				for oa in range(len(nearest_airports)):
					oa_id = airports.iloc[nearest_airports[oa]]['id']
					
					oa_xy = (airports.iloc[nearest_airports[oa]]['lat'],airports.iloc[nearest_airports[oa]]['lon'])
					oa_access_dist = geodesic(og_xy, oa_xy).m /1609
					
					#Looking up airports at the top cities									
					for da in range(len(nearest_dest_airports)):
						da_id = airports.iloc[nearest_dest_airports[da]]['id']
						
						da_xy = (airports.iloc[nearest_dest_airports[da]]['lat'],airports.iloc[nearest_dest_airports[da]]['lon'])
						da_egress_dist = geodesic(da_xy, de_xy).m /1609
						acc_egg_distance = oa_access_dist + da_egress_dist
						if G.has_node(oa_id) and G.has_node(da_id) and nx.has_path(G,source=oa_id, target=da_id):
							if (G.has_edge(oa_id,da_id)): #There's a non-stop flight
								flight_route = [oa_id,da_id]
								flight_distance = G[oa_id][da_id]['Distance']
								flight_time = G[oa_id][da_id]['Flight Time Hrs']
							else: #We need to connect
								flight_route = nx.shortest_path(G, source=oa_id, target=da_id, weight="Inverse Flights")
								flight_distance = nx.shortest_path_length(G, source=oa_id, target=da_id, weight="Distance")
								flight_time = nx.shortest_path_length(G, source=oa_id, target=da_id, weight="Flight Time Hrs")
						else:
							continue
						flight_options.append([flight_route, flight_distance, acc_egg_distance, flight_time])

			chosen_route = selectAirPath(flight_options)
			air_trips[s] = chosen_route

		routes.append(adjustAirPath(air_trips)[0])	
		pmt.append(adjustAirPath(air_trips)[1])
		pht.append(adjustAirPath(air_trips)[2])

	p['estRoute_flying'] = routes
	p['PMT_flying'] = pmt
	p['PHT_flying'] = pht

	return p

def computeGeodesicMetrics(sel,p):
	sources = list(sel[['lat','lon']].itertuples(index=False, name=None))
	destinations = list(p[['lat','lon']].itertuples(index=False, name=None))
	od_distances = []
	for d in range(len(destinations)):
		PMT_geodesic = [] #List to store the O-D level data
		for o in range(len(sel)):
			PMT_geodesic.append(geodesic(sources[o], destinations[d]).m / 1609)
		od_distances.append(PMT_geodesic)
	p['PMT_geodesic'] = od_distances
	return p

def computeDrivingMetrics(dist_df, tt_df, sel,p):

	sources = list(sel['id'])
	destinations = list(p['id'])

	distances = []
	travel_times = []
	od_distances = []
	od_travel_times = []

	# Loop through all source and destination combinations
	for d in destinations:
		PMT_driving = [] #List to store the O-D level data
		PHT_driving = [] #List to store the O-D level data
		sum_PMT_driving = 0 #Reset the totals for this potential city
		sum_PHT_driving = 0
		for o in sources:
			if not(dist_df.at[o,str(d)] is None):
				PMT_driving.append(dist_df.at[o,str(d)])
				distance = sel.iloc[sources.index(o)]['Number of attendees'] * dist_df.at[o,str(d)]
				
				PHT_driving.append(tt_df.at[o,str(d)])
				travel_time = sel.iloc[sources.index(o)]['Number of attendees'] * tt_df.at[o,str(d)]

			else:
				PMT_driving.append(None)
				distance = 0
				PHT_driving.append(None)
				travel_time = 0
			
			sum_PMT_driving = sum_PMT_driving + distance
			sum_PHT_driving = sum_PHT_driving + travel_time

		distances.append(sum_PMT_driving)
		travel_times.append(sum_PHT_driving)
		od_distances.append(PMT_driving)
		od_travel_times.append(PHT_driving)

	p['sum_PMT_driving'] = distances
	p['sum_PHT_driving'] = travel_times
	p['PMT_driving'] = od_distances
	p['PHT_driving'] = od_travel_times

	return p

def estimateModeChoice(distances, air_routes, driving_routes, attendees):
	air_pax = [] 
	car_pax = []
	#These coefficients came from fitting a curve on USDOT summary data
	c3 = 0.000000193201123
	c2 = 0.000291976066918
	c1 = 0.001028443017465
	i = 99.885525319073300
	rcs = None
	#Let's first assign them assuming everything is available
	for d in range(len(distances)):
		est_driving_dist = driving_routes[d] if driving_routes[d] != None else 1.2 * distances[d]
		if est_driving_dist < 1000:
			rcs = i + c3*(est_driving_dist**3) - c2*(est_driving_dist**2) - c1*est_driving_dist
		else:
			rcs = 0
		#print(rcs)
		if air_routes[d] == None and driving_routes[d] == None: #There are no feasible routes #distances.index(d)
			air_pax.append(None)
			car_pax.append(None)
		elif air_routes[d] == None:
			air_pax.append(0) #No one will fly because there is no route, but they might drive
			if rcs < 80: #Not likely to appeal for an event, disqualifying this option
				car_pax.append(None)
			else:
				car_pax.append(attendees[d]) #Everyone assumed to drive
		elif driving_routes[d] == None:
			car_pax.append(0)
			air_pax.append(attendees[d]) #Assume all will fly
		else: #Both driving and flying are feasible options
			air_pax.append(round(attendees[d] * (1-(rcs/100))))
			car_pax.append(attendees[d]-air_pax[-1]) #The rest of people will drive

	return [air_pax,car_pax]

def emissionsFirstPass(x): #Without using the API
	#emissions = 0 #in pounds of CO2e
	#From driving
	distance_driven = sum(list(map(lambda a,b: a*b if a>0 else 0,x['cars'],x['PMT_driving'])))
	drive_emissions = distance_driven * (car_efficiency / 2204)
	#From flying
	distance_flown = sum(list(map(lambda a,b: a*b if a>0 else 0,x['flyers'],x['PMT_flying'])))
	fly_emissions = distance_flown * 2 * (254/2204)*1.609 #https://8billiontrees.com/carbon-offsets-credits/carbon-ecological-footprint-calculators/carbon-footprint-driving-vs-flying/
	#emissions = emissions / 2204 #These many grams in a pound
	return drive_emissions + fly_emissions

def uninitiate():	
	st.session_state['key'] = 'Uninitiaded'

def pingClimateNeutral(route,dist):
	emissions = 0
	GC_call_data = {
		'segments': {},
		'cabin_class': 'economy',
		'currencies[0]': 'USD',
		}
	for i in range(len(route.split("-"))-1):
		GC_call_data["segments["+str(i)+"][origin]"] = route.split("-")[i]
		GC_call_data["segments["+str(i)+"][destination]"] = route.split("-")[i+1]

	response = requests.get(GC_API_URL,
						params=GC_call_data,
						auth=(GC_API_KEY, ''))

	if response.status_code == 200:
		response_data = json.loads(response.text)
		emissions = response_data['footprint'] * 1000 #Convert from kg to g
	else:
		emissions = dist *2 * (254) * 1.609

	return emissions

def myround(x, base=5):
    return base * round(x/base)

def emissionsSecondPass(x):
	#From driving
	distance_driven = sum(list(map(lambda a,b: a*b if a>0 else 0,x['cars'],x['PMT_driving'])))
	drive_emissions = distance_driven * car_efficiency
	#From flying
	fly_emissions = sum(list(map(lambda a,b,c: a * pingClimateNeutral(b,c) if a>0 else 0,x['flyers'],x['estRoute_flying'],x['PMT_flying'])))
	
	emissions = drive_emissions + fly_emissions
	
	emissions = emissions / 2204 #These many grams in a pound
	emissions = myround(emissions,10) #Rounding to 10 lb
	return emissions

def createPrettyCols(x):
	driving = ""
	flying = ""
	for i in range(len(selected_cities)):
		if x['carpax'][i] > 0 and x['PMT_driving'][i] > 0:
			driving = driving + str(x['carpax'][i]) + (" person" if x['carpax'][i] == 1 else " people" ) +" riding " + str(x['cars'][i]) + " car(s) from " + selected_cities[i].split(",")[0] + " (~" + '%.1f' % x['PHT_driving'][i] + " hours); "
		if x['flyers'][i] > 0 and x['PMT_flying'][i] > 0:
			flying = flying + str(x['flyers'][i]) + (" person" if x['flyers'][i] == 1 else " people" ) + " flying " + x['estRoute_flying'][i]+ " (~" + '%.1f' % x['PHT_flying'][i] + " hours); "
	if driving == "":
		driving = "No one drives"
	if flying == "":
		flying = "No one flies"
	return [driving,flying]

#Page config
st.set_page_config(
    page_title="Greca: Gathering with Reduced Emissions v0.1",
    page_icon=":coffee:",
    layout="centered",
    initial_sidebar_state="auto",
    menu_items={
        'Get help': None,
        'Report a bug': "mailto:jorge@barrios.group?subject=Issue%20with%20the%20Greca%20web%20app",
        'About': "## Sources\n* Central city locations from [Andrew Van Leuven](https://andrewvanleuven.com/post/cityshapefiles/)\n* Flight time estimates fom Prof. Bassett's [class notes](https://faculty.nps.edu/rbassett/_book/introduction-to-linear-regression.html#fitting-a-linear-model-in-r) at NPS\n* Driving distance and duration estimates from [OpenRouteService](openrouteservice.org)\n* Flying emissions estimates from [GoClimateNeutral](https://www.goclimate.com/blog/wp-content/uploads/2019/04/Calculations-in-GoClimateNeutral-Flight-Footprint-API.pdf)\n* Mode splits from basic BTS statistics on long-distance [business travel](https://www.bts.gov/archive/publications/america_on_the_go/us_business_travel/entire#:~:text=Nearly%20three%2Dfourths%20(74%25),7%25%20of%20all%20business%20trips.)\n *Likely air routes from Sep-Oct 2023 FAA data on flights between city pairs\n* Driving emissions per mile from [research](https://publications.anl.gov/anlpubs/2022/07/176270.pdf) by Argonne National Laboratory\n* Driving emissions per mile from [EPA](#https://www.epa.gov/greenvehicles/greenhouse-gas-emissions-typical-passenger-vehicle)"
    }
)

# Initialization
if 'key' not in st.session_state:
    st.session_state['key'] = 'Uninitiaded'

cola,colb = st.columns([0.8,0.2])
with cola:
	st.markdown("# Greca")
	st.markdown("**G**athering with **Re**duced **E**missions **Ca**lculator v0.1")
with colb:
	st.image("Greca.png", width=200, use_column_width="auto")
st.divider()
st.markdown("Planning an \"off-site\" gathering for your team? Use this simple tool to estimate the carbon emissions resulting from travel to and from the gathering. It also tallies travel time/distance for attendees.")
st.markdown("The tool is easy to use:")
st.markdown("1. Select the \"origin\" cities, where attendees reside.\n2. Click the \"Calculate impacts\" button to get possible locations and an estimate of the impacts.\n3. Edit the results as you see fit to better match how your team would actually travel.")
st.markdown("This first version only covers US cities and driving and flying modes.")

cities = pd.read_csv("output_cities.csv")
distances = pd.read_csv("geodesic_distances.csv")

#st.map(cities)
selected_cities = st.multiselect("#### Enter origin cities", cities['Name'].sort_values(), on_change=None, placeholder="Choose all cities")
cola,colb = st.columns(2)
rt_toggle = 2 #Accounting for round trips in final table
sel_toggle = st.toggle("Limit choices to origin cities?", value=False)

airport_access_driving_speed = 45 #mi/hr
airport_access_security = 1 #hr
layover_duration = 0.75 #hr
driving_gCO2_per_mi = 400 #https://www.epa.gov/greenvehicles/greenhouse-gas-emissions-typical-passenger-vehicle
min_flight_distance = 50 #mi

with st.expander(":nerd_face: Open to tweak obscure parameters for the analysis"):
	col1, col2 = st.columns(2)
	with col1:
		pop_weight = 50 #st.slider("Weight given to population vs just distance",0,100, value=50, step=25)
		bb_buffer = st.slider("Geographic buffer %",0,100, value=50, step=25, help="Expands the bounding box of potential cities to be analyzed")
		first_filter_top_pctile = st.slider("Top percentile cities for first cut",0,100, value=20, step=10,help="This controls how many cities are advanced into more detailed analyses")/100
	with col2:
		carpooling_propensity = st.slider("People per car", 1,5, value=2, help="Max number of people driving together. In other words, how comfortable are people carpooling?")
		car_efficiency = st.slider("Driving emissions per mile (g CO2e/mi)", 200,500,value=400,step=50, help="Range of values based on US DoE [research](https://www.energy.gov/eere/vehicles/articles/fotw-1208-oct-18-2021-life-cycle-greenhouse-gas-emissions-2020-electric), the default is a small gas SUV.")

	
input_dict = {'City': selected_cities, 'Number of attendees': [1] * len(selected_cities)} 
button_dis = True
if len(selected_cities) > 0:
	st.write("#### Enter attendee counts:")
	input_df = pd.DataFrame(input_dict)
	edited_input_df = st.data_editor(input_df, hide_index=True,on_change=uninitiate())
	button_dis = False

# Submit button
prog_value = 0
if st.button("Calculate impacts",disabled=button_dis):
	
	input_airports = pd.read_csv("airport-codes.csv")#, nrows=5)
	input_airports['id'] = input_airports['iata_code']
	airports = gpd.GeoDataFrame(input_airports, geometry=gpd.points_from_xy(input_airports.lon, input_airports.lat), crs="EPSG:4326")
	airports.to_crs("3857",inplace=True)

	airport_pairs = pd.read_csv("airport_pairs.csv", thousands=',')#, nrows=5)

	#Create the graph from the observed airplane data
	G = nx.from_pandas_edgelist(airport_pairs,source="Departure",target="Arrival",edge_attr=["Flights","Inverse Flights","Distance", "Flight Time Hrs"],create_using=nx.DiGraph())


	edited_input_df = pd.merge(edited_input_df,cities,left_on="City", right_on="Name")
	if sel_toggle:
		cities = cities[cities['Name'].isin(list(edited_input_df['Name']))] #Filter choices to only the origin cities
		first_filter_top_pctile = 1.0
	filtered_cities = filterCities(edited_input_df,cities,bb_buffer)

	top_cities = rankCities(edited_input_df,filtered_cities)

	sel_gpd = gpd.GeoDataFrame(edited_input_df, geometry=gpd.points_from_xy(edited_input_df.lon, edited_input_df.lat), crs="EPSG:4326")
	prog_bar = st.progress(prog_value, text="Working on the analysis...")

	
	driv_dist_df = pd.read_csv("driv_distances_matrix.csv").set_index('id')
	driv_time_df = pd.read_csv("driv_times_matrix.csv").set_index('id')
	
	top_cities = computeGeodesicMetrics(edited_input_df, top_cities)
	top_cities = computeDrivingMetrics(driv_dist_df, driv_time_df, edited_input_df, top_cities)
	
	top_cities = computeFlightMetrics(sel_gpd,top_cities)

	prog_bar.empty()
	st.write("### Map of potential cities")

	top_cities['flyers'] = top_cities.apply(lambda x: estimateModeChoice(x['PMT_geodesic'],x['estRoute_flying'],x['PMT_driving'],list(edited_input_df['Number of attendees']))[0], axis=1)#lambda x: list(map(lambda x, y: round(x*y), x['air_shares'],list(edited_input_df['Number of attendees']))),axis=1)
	top_cities['carpax'] = top_cities.apply(lambda x: estimateModeChoice(x['PMT_geodesic'],x['estRoute_flying'],x['PMT_driving'],list(edited_input_df['Number of attendees']))[1], axis=1)#top_cities.apply(lambda x: list(map(lambda x, y, z: y-x if z != None else 0, x['flyers'],list(edited_input_df['Number of attendees']),x['PMT_driving'])),axis=1)
	
	#Remove any rows with None flyers or car passengers
	top_cities['valid'] = top_cities.apply(lambda x: True if sum(filter(None, x['flyers'])) + sum(filter(None, x['carpax'])) == edited_input_df['Number of attendees'].sum() else False,axis=1)
	top_cities = top_cities[top_cities['valid']]
	if top_cities.empty:
		st.warning("Sorry, couldn't find any suitable options")
		st.stop()

	top_cities['cars'] = top_cities.apply(lambda x: list(map(lambda x: math.ceil(x/carpooling_propensity), x['carpax'])),axis=1)
	
	top_cities['emissionsEst'] = top_cities.apply(lambda x: emissionsFirstPass(x), axis=1)
	

	top_cities['color'] = '#ad2636'

	top_cities['rank'] = top_cities['emissionsEst'].rank(ascending=True) #The strongest potential is in lower scores
	top_cities.sort_values(by='rank', ascending=True, inplace=True)

	top_cities['drivingPretty'] = top_cities.apply(lambda x: createPrettyCols(x)[0],axis=1)
	top_cities['flyingPretty'] = top_cities.apply(lambda x: createPrettyCols(x)[1],axis=1)

	output_df = top_cities[['Name','PMT_driving','PHT_driving','PMT_flying','PHT_flying','estRoute_flying','flyers','carpax','cars','color','lat','lon','emissionsEst','drivingPretty','flyingPretty']].head(20) #Top 10 choices
	st.session_state['key'] = 'Initiated'

if st.session_state['key'] == 'Initiated':
	edited_input_df['color'] = '#5aa800'
	try:
		st.map(pd.concat([output_df,edited_input_df]),color="color")
	except Exception as e:
		print(e)
		st.map(pd.concat([output_df,edited_input_df]))
	
	with st.spinner('Pulling airplane travel emissions'):
		output_df['emissions'] = output_df.apply(lambda x: emissionsSecondPass(x)* rt_toggle, axis=1) 
	st.toast('Done!',icon='🏁')

	output_df['Rank'] = output_df['emissions'].rank(ascending=True) #The strongest potential is in lower scores
	output_df['PHT'] = output_df.apply(lambda r: sum(list(map(lambda x,y,a,b: myround(x*y if x>0 else 0 + a*b if a>0 else 0,0.1) * rt_toggle,r['carpax'],r['PHT_driving'],r['flyers'],r['PHT_flying']))),axis=1)
	output_df['PMT'] = output_df.apply(lambda r: sum(list(map(lambda x,y,a,b: myround(x*y if x>0 else 0 + a*b if a>0 else 0,0.1) * rt_toggle,r['carpax'],r['PMT_driving'],r['flyers'],r['PMT_flying']))),axis=1)
	output_df.sort_values(by='Rank', ascending=True, inplace=True)
	
	cols = output_df.columns.to_list()
	cols = cols[-1:] + cols[:-1]
	output_df = output_df[cols]

	column_config_data={
		"emissions": st.column_config.ProgressColumn(
			"Total Emissions",
			help="Emissions in pounds of CO2 equivalent",
			format="%d lbs",
			min_value=0,
			max_value=1.1*max(output_df['emissions'])
			),
		'PHT': st.column_config.ProgressColumn(
			"Total Travel Time",
			help="Aggregate travel time in hours",
			format="%d.1 hrs",
			min_value=0,
			max_value=1.1*max(output_df['PHT'])
			),
		'PMT': st.column_config.ProgressColumn(
			"Total Person Miles",
			help="Aggregate distance traveled in miles",
			format="%d mi",
			min_value=0,
			max_value=1.1*max(output_df['PMT'])
			),
		'drivingPretty': st.column_config.TextColumn(
			"Driving Assumptions",
			#width="large",
			help="The expected number of people and cars driven"
			),
		'flyingPretty': st.column_config.TextColumn(
			"Flying Assumptions",
			#width="large",
			help="The expected number of people and routes flown"
			)}

	moneyCols = ['Rank','Name','emissions','PHT','PMT','drivingPretty','flyingPretty']
	st.dataframe(output_df[moneyCols], column_config=column_config_data, hide_index=True)

	st.metric(
		label=":factory: Lowest emissions (lb CO2e) come from gathering in " + output_df.iloc[0]['Name'],
		value='%0d lb CO2e' % output_df.iloc[0]['emissions'],
		help="For comparison, a typical passenger vehicle emits about 10K lbs of CO2 per year."
	)
	
	st.session_state['key'] = 'Complete'

	if st.session_state['key'] == 'Complete':
		with st.expander(":leaves: Open to see more tips for sustainable travel"):
			st.markdown("There are a few ways to reduce the impact of work travel. Here are a few I usually consider:")
			st.markdown("* The most reductions come from *not* traveling and doing things remotely, which has improved but it's not a substitute for in-person interaction (in my opinion)\n    * A compromise might be to do an in-person version every 3-4 gatherings.\n    * Another idea is to break up the gathering into 2-3 mini-gatherings connected remotely to one another.\n* Look for intercity transit options, most likely they'll be the least impactful way to travel.\n* If you're flying, look for low-cost carriers, direct flights, and convenient public transit at the origin and destination airports.\n* If you're driving, use a fuel-efficient or electrified car and carpool as much as possible.")

