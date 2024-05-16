#This file contains a simplified HVAC system case study
#This corresponds to the P1 unsafe hyper-property in our paper resulting in the system being unsafe
#'Towards SMT-Based Verification of Safety Hyper-Properties in Hybrid Automaton'
from z3 import *
import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from hybrid_specification import Specification 

#passing parameter of the location names to create array of enum of locations
locations = ['L1','L2']
spec = Specification(locations)

temperature = Real('temperature')

#use spec.Location to access the enumerated data type 
#use spec.locations to access the SMT enumerated location 
# constant L1 and L2 
location = Const("location",spec.Location)

#need to pass this dictionary of variables and locations to the 
#instance of the specification
variables = {'temperature':temperature}
locations = {'location':location}

#create instance of hybrid specification
spec.create_variables(variables,locations)

#number of quantifiers correspond to the number of trace quantifiers in the hyper-property
num_quantifiers = 2
#initial condition 
initial_condition = And(temperature>=60,temperature<=70,location==spec.locations[0])

#transitions is an array of dictionaries
#create transitions in the following format with the dictionary keys corresponding to 
#'guard', 'update', 'locationInvariant'
transitions = []
#discrete transition: Transition from location 1 to location 2
transition_1 = {}
transition_1['guard'] = And((location==spec.locations[0]),(temperature<=62))
transition_1['update'] = {'location':spec.locations[1]}
#discrete transition: Transition from location 2 to location 1
transition_2 = {}
transition_2['guard'] = And((location==spec.locations[1]),(temperature>=68))
transition_2['update'] = {'location':spec.locations[0]}

#Do not use literals such as {'temperature':-2} as -2 
#can be interpreted as a Python number, thus use RealVal 
#if dynamic is a constant
#the update essentially represents an ODE
#continuous transition 1: Controller location 1
transition_3 = {}
transition_3['locationInvariant'] = And((location==spec.locations[0]),(temperature>=60))
transition_3['update'] = {'temperature':RealVal(-2)}

#continuous transition 2: Controller location 2
transition_4 = {}
transition_4['locationInvariant'] = And((location==spec.locations[1]),(temperature<=70))
transition_4['update'] = {'temperature': 0.6*(70-temperature)}

transitions.append(transition_1)
transitions.append(transition_2)
transitions.append(transition_3)
transitions.append(transition_4)

variable_dict, time_dict, location_dict = spec.create_specification(initial_condition,transitions,num_quantifiers)

#safety property
unsafe_formula = And((time_dict['time'][0]==time_dict['time'][1]),Not(location_dict['location'][1]==location_dict['location'][0]),Not(variable_dict['temperature'][0]==variable_dict['temperature'][1]))

#backward reachability returns safe
spec.check_reachability(unsafe_formula,num_quantifiers)

