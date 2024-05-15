#This file contains a simplified HVAC system case study
#This corresponds to the P1 unsafe hyper-property in our paper resulting in the system being unsafe
#'Towards SMT-Based Verification of Safety Hyper-Properties in Hybrid Automaton'

from z3 import *
import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from backward_reachable import BackwardReachable

#passing parameter of the location names to create array of enum of locations
location_names = ['L1', 'L2']
system = BackwardReachable(location_names)

temperature = Array('temperature',IntSort(),RealSort())
temperature_1 = Array('temperature_1',IntSort(),RealSort())
location = Array('location',IntSort(),system.Location)
location_1 = Array('location_1',IntSort(),system.Location)
time = Array('time',IntSort(),RealSort())
time_1 = Array('time_1',IntSort(),RealSort())
delay = Real('delay')
delay_1 = Real('delay_1')
current_variables = {'temperature':Array('temperature',IntSort(),RealSort())}
current_location = {'location':Array('location',IntSort(),system.Location)}
current_time = {'time':Array('time',IntSort(),RealSort())}
current_delay = {'delay':Real('delay')}
current_intermediate_delay = {'delay_1':Real('delay_1')}


#Unsafe property
unsafe = And((time[0]==time[1]),Not(location[1]==location[0]),Not(temperature[0]==temperature[1]))
print(unsafe)

#initial condition
initial = None
for i in range(2):
    if initial is None:
        initial = And((temperature[i]>=60),(temperature[i]<=70),(time[i]==0),(location[i]==system.location_constants[0]))
    else:
        initial = And(initial,And((temperature[i]>=60),(temperature[i]<=70),(time[i]==0),(location[i]==system.location_constants[0])))

#transitions
transitions = []  

#number of quantifiers correspond to the number of trace quantifiers in the hyper-property
quantifiers_num = 2  
for i in range(quantifiers_num):
    unchanged = And([And(temperature_1[j] == Select(temperature, j), 
                         location_1[j] == Select(location, j), 
                         time_1[j] == Select(time, j),(time_1[j]>=0))
                     for j in range(quantifiers_num) if j != i])
    
    #continuous transition 1: Controller location 1
    transitions.append(
        And(
            Not(And((delay_1 > 0),(delay_1 <= delay),Not(((temperature[i] + (-2*delay_1))>=60)))),
            ((temperature[i] + (-2*delay))>=60),
            (location[i]==system.location_constants[0]),
            (temperature_1[i]==temperature[i]+ (-2 * delay)),
            (time_1[i]==time[i]+delay),(delay>0),
            (location_1[i]==system.location_constants[0]),
            (time_1[i]>0),
            unchanged
            )
        )

    #continuous transition: Controller location 2
    transitions.append(
        And(
            Not(And((delay_1 > 0),(delay_1 <= delay),Not(((temperature[i]+(0.6*delay_1*(70-temperature[i])))<=70)))),
            ((temperature[i]+(0.6*delay*(70-temperature[i])))<=70),
            (location[i]==system.location_constants[1]),
            (temperature_1[i]==temperature[i]+(0.6*delay*(70-temperature[i]))),
            (time_1[i]==time[i]+delay),(delay>0),
            (location_1[i]==system.location_constants[1]),
            (time_1[i]>0),
            unchanged
            )
        )
    
    #discrete transition: Transition from location 1 to location 2
    transitions.append(And((location[i]==system.location_constants[0]),(location_1[i]==system.location_constants[1]),(temperature[i]<=62),(temperature_1[i]==temperature[i]),(time_1[i]==time[i]),(time_1[i]>0),unchanged))
    #discrete transition: Transition from location 2 to location 1
    transitions.append(And((location[i]==system.location_constants[1]),(location_1[i]==system.location_constants[0]),(temperature[i]>=68),(temperature_1[i]==temperature[i]),(time_1[i]==time[i]),(time_1[i]>0),unchanged))

#backward reachability returns unsafe
safety = system.reachable(current_variables,current_location,current_time,current_delay,current_intermediate_delay,initial,transitions,unsafe,2)
if safety==False:
    print("System is unsafe")
else:
    print("SYSTEM IS SAFE !")
