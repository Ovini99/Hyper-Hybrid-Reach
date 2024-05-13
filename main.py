from z3 import *
from backward_reachable import BackwardReachable

location_names = ['L1', 'L2']
system = BackwardReachable(location_names)

#Temperature control example
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

# print(current_variables)
# print(current_location)

#safety property
# unsafe = If((temperature[0]>=temperature[1]),((temperature[0]-temperature[1])>10),((temperature[1]-temperature[0])>10))
unsafe = Or((And(temperature[0]>=temperature[1],((temperature[0]-temperature[1])>10))),(And((temperature[1]>temperature[0]),(temperature[1]-temperature[0]>10))))

#Unsafe property
# unsafe = And((time[0]==time[1]),Not(location[1]==location[0]),Not(temperature[0]==temperature[1]))
print(unsafe)
initial = None
for i in range(2):
    if initial is None:
        initial = And((temperature[i]>=60),(temperature[i]<=70),(time[i]==0),(location[i]==system.location_constants[0]))
    else:
        initial = And(initial,And((temperature[i]>=60),(temperature[i]<=70),(time[i]==0),(location[i]==system.location_constants[0])))

# print("Initial: ", initial)


transitions = []  

#unsafe system
quantifiers_num = 2  
for i in range(quantifiers_num):
    unchanged = And([And(temperature_1[j] == Select(temperature, j), 
                         location_1[j] == Select(location, j), 
                         time_1[j] == Select(time, j),(time_1[j]>=0))
                     for j in range(quantifiers_num) if j != i])
    
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

    # transitions.append(And(((temperature[i] + (-2*delay))>=60),(location[i]==L1),(temperature_1[i]==temperature[i]+ (-2 * delay)),(time_1[i]==time[i]+delay),(delay>0),(location_1[i]==L1),(time_1[i]>0),unchanged))
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
    # transitions.append(And(((temperature[i]+delay)<=70),(location[i]==L2),(temperature_1[i]==temperature[i]+delay),(time_1[i]==time[i]+delay),(delay>0),(location_1[i]==L2),(time_1[i]>0),unchanged))
    transitions.append(And((location[i]==system.location_constants[0]),(location_1[i]==system.location_constants[1]),(temperature[i]<=62),(temperature_1[i]==temperature[i]),(time_1[i]==time[i]),(time_1[i]>0),unchanged))
    transitions.append(And((location[i]==system.location_constants[1]),(location_1[i]==system.location_constants[0]),(temperature[i]>=68),(temperature_1[i]==temperature[i]),(time_1[i]==time[i]),(time_1[i]>0),unchanged))
# print(transitions)

# # initial safety check
# safety = safety_check(unsafe,initial)

safety = system.reachable(current_variables,current_location,current_time,current_delay,current_intermediate_delay,initial,transitions,unsafe,2)
if safety==False:
    print("System is unsafe")
else:
    print("SYSTEM IS SAFE !")

# num_elem = 2
# current_state = unsafe
# preimage_set = None
# old_states = None
# original_state_list = {**current_variables,**current_location}
# original_scalar = create_scalar_vars_for_elements(original_state_list,2)
# immediate_previous_state_set = None
# current_variables, current_location, current_time, current_delay, state, old_state_list, preimage_set,immediate_previous_state_set = preimage_compute(current_variables,current_location,current_time,current_delay,
#                                                                                                     current_state,transitions,preimage_set,immediate_previous_state_set)

# current_state_list = {**current_variables,**current_location,**current_time}
# if old_states == None:
#             old_states = current_state
# else:
#     old_states = Or(old_states,current_state)

# current_state=state
# delay_list = list(current_delay.values())

# fixed_point(current_state,old_states,current_state_list,delay_list,old_state_list,original_scalar,num_elem)

# transitions = []

# for i in range(1):
#     unchanged = And([And(temperature_1[j] == Select(temperature, j), 
#                          location_1[j] == Select(location, j), 
#                          time_1[j] == Select(time, j),time_1[j]>=0)
#                      for j in range(quantifiers_num) if j != i])
#     transitions.append(And(((temperature[i] + (-2*delay))>=60),(location[i]==L1),(temperature_1[i]==temperature[i]+ (-2 * delay)),(time_1[i]==time[i]+delay),(delay>0),(location_1[i]==L1),(time_1[i]>0),unchanged))

# current_variables, current_location, current_time, current_delay, state, old_state_list, preimage_set, immediate_previous_state_set = preimage_compute(current_variables,current_location,current_time,current_delay,
#                                                                                                     current_state,transitions,preimage_set,immediate_previous_state_set)

# current_state_list = {**current_variables,**current_location,**current_time}
# if old_states == None:
#             old_states = current_state
# else:
#     old_states = Or(old_states,current_state)

# current_state=state

# fixed_point(current_state,old_states,current_state_list,delay_list,old_state_list,original_scalar,num_elem)

# current_variables, current_location, current_time, current_delay, state, old_state_list, preimage_set, immediate_previous_state_set = preimage_compute(current_variables,current_location,current_time,current_delay,
#                                                                                                     current_state,transitions,preimage_set,immediate_previous_state_set)

# current_variables, current_location, current_time, current_delay, state, old_state_list, preimage_set, immediate_previous_state_set = preimage_compute(current_variables,current_location,current_time,current_delay,
#                                                                                                     current_state,transitions,preimage_set,immediate_previous_state_set)