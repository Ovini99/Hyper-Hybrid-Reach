#this file contains the safety point and fixed point checks
#and pre-image computation functions 
from z3 import *

class BackwardReachable:
    def __init__(self, location_names,delay_var,delay_1_var):
        self.Location, self.location_constants = EnumSort('Location', location_names)
        self.pre_image_num = 0
        self.delay = delay_var
        self.delay_1 = delay_1_var

    #safety-point check between initial and current state
    def safety_check(self, current_state,initial):
        solver = Solver()
        solver.reset()
        if current_state==None:
            print("This is a unique condition of not being able to backwardly reach any state starting from unsafe states,thus the system does not violate the safety property")
            print("SYSTEM IS SAFE")
            return True
        solver.add(initial)
        solver.add(current_state)

        if solver.check() == sat:
            # Initial state overlaps with unsafe state
            print("SYSTEM IS UNSAFE !")
            print("Model of unsafe system: ",solver.model())
            return False
        else:
            print("System is not unsafe for now...")
            return True
    
     #Creates substitution pairs for substituting array indices with scalar variables.
    def create_substitution_pairs(self, array_dict, scalar_vars,num_elements):
        substitutions = []
        for key, array in array_dict.items():
            for idx in range(num_elements):  
                scalar_var_name = f"{key}_e{idx}"
                if scalar_var_name in scalar_vars:
                    substitutions.append((array[idx], scalar_vars[scalar_var_name]))
        return substitutions
    
    def create_scalar_vars_for_elements(self, variable_dict, num_elements):
        scalar_vars = {}
        for key, arr in variable_dict.items():
            for idx in range(num_elements):
                var_name = f"{key}_e{idx}"
                if arr.range() == RealSort():
                    scalar_vars[var_name] = Real(var_name)
                elif arr.range() == self.Location: 
                    scalar_vars[var_name] = Const(var_name, self.Location)
                else:
                    raise ValueError("Unsupported type for automatic scalar variable creation")
        return scalar_vars
    
    #checks if fixed point is reached
    #checks that if there exists a state that satisfies the current state
    #AND NOT the old states
    def fixed_point(self,current_state,old_states,current_state_vars,delay_list,intermediate_delay_list,old_state_vars,original_vars,num_elem):
        if old_states==None:
            print("Initial check, nothing to check...")
            return False
        
        if current_state==None:
            print("Fixed point reached, no more old states added")
            return True
        
        solver = Solver()
        solver.reset()

        scalar_old_state_variables = self.create_scalar_vars_for_elements(old_state_vars,num_elem)

        substitution_pairs_old = self.create_substitution_pairs(old_state_vars,scalar_old_state_variables,2)

        exists_old_dict = {key: value for key, value in scalar_old_state_variables.items() if key not in original_vars}
        exists_old_list = []
        if not exists_old_dict:
            exists_old_list=[]
        else:
            exists_old_list=list(exists_old_dict.values())
            exists_old_list = exists_old_list + delay_list + intermediate_delay_list

        scalar_current_state_variables = self.create_scalar_vars_for_elements(current_state_vars,num_elem)
        
        substitution_pairs_new = self.create_substitution_pairs(current_state_vars,scalar_current_state_variables,2)

        exists_new_dict = {key: value for key, value in scalar_current_state_variables.items() if key not in original_vars}
        exists_new_list = list(exists_new_dict.values())
        exists_new_list = exists_new_list + delay_list + intermediate_delay_list

        substituted_old_backward_reach = substitute(old_states,*substitution_pairs_old)

        substituted_new_backward_reach = substitute(current_state,*substitution_pairs_new)

        projected_backward_reach = []
        if not exists_old_list:
            projected_backward_reach = substituted_old_backward_reach
        else:
            projected_backward_reach = Exists(exists_old_list,substituted_old_backward_reach)

        projected_new_backward_reach = Exists(exists_new_list,substituted_new_backward_reach)

        solver.add(projected_new_backward_reach)
        solver.add(Not(projected_backward_reach))
        # If UNSAT, it means there does NOT exist a state that satisfies 
        # current state but not old states,
        # implying current state is fully covered by backward_reach 
        # (fixed point reached).
        if solver.check() == unsat:
            print("Fixed point reached")
            print(solver.to_smt2())
            return True 
        else:
            print("New states introduced during fixed point")
            return False
    
    #pre-image computation
    def preimage_compute(self,current_variables, current_location, current_time, current_delay, current_intermediate_delay ,current_state, transitions,preimage_set,immediate_previous_state_set):
        self.pre_image_num = self.pre_image_num + 1
        solver = Solver()
        oldState = None
        new_preimage_set = []
        new_immediate_previous_state_set = []
        old_variables = {**current_variables,**current_location,**current_time}
        print("Preimage computation")

        #Substitution pairs for location variables
        primed_locations = {f"{key}_1": Array(f'{key}_1', IntSort(), self.Location) for key in current_location}
        
        #Substitution pairs for integer variables
        primed_variables = {f"{key}_1": Array(f'{key}_1', IntSort(), RealSort()) for key in current_variables}

        #Substitution pairs for time 
        primed_time = {f"{key}_1": Array(f'{key}_1', IntSort(), RealSort()) for key in current_time}
        
        # Combine pairs into subs_pairs list
        subs_pairs = [(current_variables[key], primed_variables[f"{key}_1"]) for key in current_variables] \
                    + [(current_location[key], primed_locations[f"{key}_1"]) for key in current_location] \
                    + [(current_time[key], primed_time[f"{key}_1"]) for key in current_time]    

        transit_int = 0
        #find pre-images
        if preimage_set is None:
            print("First pre-image")
            # Perform the substitution in transition
            substituted_state = substitute(current_state, *subs_pairs)
            print("Substituted current state: ",substituted_state)
            for transition in transitions:
                transit_int = transit_int + 1

                delay_len = len(current_delay)
                new_key = f'delay{delay_len}'
                new_intermediate_key = f'delay_1_{delay_len}'
                current_delay[new_key]= Real(new_key)
                current_intermediate_delay[new_intermediate_key] = Real(new_intermediate_key)
                transition_1 = substitute(transition,(self.delay,current_delay[f'delay{delay_len}']))
                transition_1 = substitute(transition_1,(self.delay_1,current_intermediate_delay[f'delay_1_{delay_len}']))

                solver.reset()
                constraint = And(transition_1,substituted_state)
                solver.add(constraint)
                if solver.check() == sat:
                    new_preimage_set.append(constraint)

                    transition_track = []
                    transition_track.append(transit_int)
                    new_immediate_previous_state_set.append(transition_track)

                    if oldState==None:
                        oldState = constraint
                    else:
                        oldState = Or(oldState,constraint)
        else:
            print("Next pre-image ",self.pre_image_num)
            state_int = 0
            previous_image_num = 0
            for state in preimage_set:
                transit_int = 0
                state_int = state_int + 1 
                substituted_state = substitute(state, *subs_pairs)

                for transition in transitions:
                    transit_int = transit_int + 1

                    previous_image_num = state_int - 1
                    pre_image_image = immediate_previous_state_set[previous_image_num]

                    #substitution of delay variable with a new variable
                    delay_len = len(current_delay)
                    new_key = f'delay{delay_len}'
                    new_intermediate_key = f'delay_1_{delay_len}'
                    current_delay[new_key]= Real(new_key)
                    current_intermediate_delay[new_intermediate_key] = Real(new_intermediate_key)
                    transition_1 = substitute(transition,(self.delay,current_delay[f'delay{delay_len}']))
                    transition_1 = substitute(transition_1,(self.delay_1,current_intermediate_delay[f'delay_1_{delay_len}']))

                    solver.reset()
                    constraint = And(transition_1,substituted_state)
                    solver.add(constraint)
                    if solver.check() == sat:
                        previous_state_int = state_int -1
                        if transit_int in immediate_previous_state_set[previous_state_int]:
                            continue
                        new_preimage_set.append(constraint)

                        new_pre_image_image = pre_image_image.copy()
                        new_pre_image_image.append(transit_int)
                        new_immediate_previous_state_set.append(new_pre_image_image)
                        if oldState==None:
                            oldState = constraint
                        else:
                            oldState = Or(oldState,constraint)
            
        # Dictionary of new current variables
        current_variables.update(primed_variables)
        current_location.update(primed_locations)
        current_time.update(primed_time)

        #return current state in DNF 
        #if oldState is empty pass the current state and thus reaching a fixed point...
        return current_variables, current_location, current_time, current_delay, current_intermediate_delay, oldState, old_variables, new_preimage_set, new_immediate_previous_state_set
    
    #backward reachability algorithm
    def reachable(self,current_variables,current_location,current_time, current_delay, current_intermediate_delay ,initial,transitions,unsafe,num_elem):
    #initial check between unsafe and initial states
        current_state = unsafe
        current_state_list = {**current_variables,**current_location,**current_time}
        # print("Current state list: ",current_state_list)
        old_states = None
        old_state_list = None
        state = None
        immediate_previous_state_set = None
        original_state_list = {**current_variables,**current_location}
        original_scalar = self.create_scalar_vars_for_elements(original_state_list,num_elem)
        delay_list = list(current_delay.values())
        intermediate_delay_list = list(current_intermediate_delay.values())
        preimage_set = None
        while (self.safety_check(current_state,initial) and not(self.fixed_point(current_state,old_states,current_state_list,delay_list,intermediate_delay_list,old_state_list,original_scalar,num_elem))):
            current_variables, current_location, current_time, current_delay,current_intermediate_delay, state, old_state_list, preimage_set,immediate_previous_state_set = self.preimage_compute(current_variables,current_location,current_time,current_delay,current_intermediate_delay,
                                                                                                        current_state,transitions,preimage_set,immediate_previous_state_set)
            current_state_list = {**current_variables,**current_location,**current_time}
            if old_states == None:
                old_states = current_state
            else:
                old_states = Or(old_states,current_state)
            current_state=state
            delay_list = list(current_delay.values())
            intermediate_delay_list = list(current_intermediate_delay.values())
        return self.safety_check(current_state,initial)