# the user creates an instance of this class and provided with
#the parameters of a hybrid automaton, initial state and transitions 
#this file creates an extended hybrid automaton for verification of hyper-properties
#this file also calls the backward reachability algorithm
from z3 import *
from backward_reachable import BackwardReachable

class Specification:
    def __init__(self,location_names):
        self.delay = Real('delay')
        self.delay_1 = Real('delay_1')
        self.time = Array('time',IntSort(),RealSort())

        self.backward_reach = BackwardReachable(location_names,self.delay,self.delay_1)
        self.Location = self.backward_reach.Location
        self.locations = self.backward_reach.location_constants

        self.current_variables = None
        self.current_locations = None
        self.current_time = None
        self.current_delay = None
        self.current_intermediate_delay = None

        self.primed_variables = None
        self.primed_locations = None
        self.primed_time = None

        self.variable_mapping = None
        self.location_mapping = None

        self.original_vars = None
        self.original_locations = None

        self.initial = None
        self.transitions = []
    
    #this function creates array version of variables with length of array to be
    #number of trace quantifiers
    def create_variables(self,variables,locations):
        if variables is None:
            print("Empty dictionary, include variables")
        for key,value in variables.items():
            if not value.is_real():
                print("Error: All variables need to be type real")
                return None

        #array of current variables
        self.original_vars = variables
        self.original_locations = locations
        self.current_variables = {key: Array(key, IntSort(), RealSort()) for key in variables}
        self.variable_mapping = {value: Array(key, IntSort(), RealSort()) for key,value in variables.items()}
        # print("Current variables: ",self.current_variables)
        # print("Variable mapping: ",self.variable_mapping)

        #array of current locations
        self.current_locations = {key:Array(key,IntSort(),self.Location) for key in locations}
        self.location_mapping = {value: Array(key,IntSort(),self.Location) for key,value in locations.items()}
        # print("Current locations: ",self.current_locations)
        # print("Location mapping: ",self.location_mapping)

        #array of current time
        self.current_time = {'time':self.time}
        # print("Current time: ",self.current_time)

        #array of current delay
        self.current_delay = {'delay':self.delay}
        # print("Current delay: ",self.current_delay)

        #array of intermediate delay
        self.current_intermediate_delay = {'delay_1':self.delay_1}
        # print("Current intermediate delay: ",self.current_intermediate_delay)
    
    #this creates the extended hybrid automaton specification
    def create_specification(self,initial,transitions,num_quantifiers):
        
        substituted_initial_cond = None

        prime_variables = {key:Array(f'{key}_1',IntSort(),RealSort()) for key in self.current_variables}
        prime_locations = {key:Array(f'{key}_1',IntSort(),self.Location) for key in self.current_locations}
        prime_time = {key:Array(f'{key}_1',IntSort(),RealSort()) for key in self.current_time}
        # print(prime_variables)
        # print(prime_locations)

        self.primed_variables = {self.current_variables[key]:prime_variables[key] for key in self.current_variables}
        self.primed_locations = {self.current_locations[key]:prime_locations[key] for key in self.current_locations}
        self.primed_time = {self.current_time[key]:prime_time[key] for key in self.current_time}
        # print("Primed variables: ",self.primed_variables)
        # print("Primed locations: ",self.primed_locations)
        # print("Primed time: ",self.primed_time)

        #creates initial 
        for i in range(num_quantifiers):
            substituted_vars = [(key,value[i]) for key,value in self.variable_mapping.items()]\
                                + [(key,value[i]) for key,value in self.location_mapping.items()]
            # print(substituted_vars)
            substituted_initial_cond = And(substitute(initial,substituted_vars),(self.time[i]==0))
            # print(substituted_initial_cond)
            # substituted_initial_cond = And(substituted_initial_cond,)
            if self.initial is None:
                self.initial = substituted_initial_cond
            else:
                self.initial = And(self.initial,substituted_initial_cond)
            
            
            unchanged = And([And(
                And([self.primed_variables[value][j] == value[j] for key,value in self.current_variables.items()]\
                    +[self.primed_time[self.time][j] == self.time[j]]\
                        + [self.primed_locations[value][j] == value[j] for key,value in self.current_locations.items()]))
                    for j in range(num_quantifiers) if j != i])
            # print("Unchanged: ",unchanged)

            for transition in transitions:
                if 'guard' in transition and transition['guard'] is not None:
                    susbtituted_guard = substitute(transition['guard'],substituted_vars)
                    updated_vars = And([self.primed_variables[value][i] == value[i] for key,value in self.current_variables.items()]\
                                               +[self.primed_time[self.time][i] == self.time[i]]\
                                               +[self.primed_time[self.time][i] > 0]\
                                                +[self.primed_locations[self.current_locations[key]][i] == value for key,value in transition['update'].items()])
                    # print("Substituted guard: ",susbtituted_guard)
                    # print("Updated vars: ",updated_vars)
                    transition_cond = And(susbtituted_guard,updated_vars,unchanged)
                    # print("discrete transition: ",transition_cond)
                    self.transitions.append(transition_cond)
                elif 'locationInvariant' in transition and transition['locationInvariant'] is not None:
                    # print("continuous transition")
                    substituted_update = {key: substitute(value,substituted_vars) for key,value in transition['update'].items()}
                    # print("Substituted update: ",substituted_update)
                    susbtituted_locationInvariant = substitute(transition['locationInvariant'],substituted_vars)
                    # print("Substituted location invariant: ",susbtituted_locationInvariant)

                    updates={}
                    substituted_location_invariant = susbtituted_locationInvariant
                    substituted_location_invariant_original_delay = susbtituted_locationInvariant
                    for key in substituted_update:
                        update_key=self.variable_mapping[self.original_vars[key]][i]
                        #Euler numerical approximation
                        update_formula = self.variable_mapping[self.original_vars[key]][i] + (self.delay*substituted_update[key])
                        updated_formula = self.primed_variables[self.current_variables[key]][i] == update_formula
                        # print(update_formula)
                        updates[update_key]=updated_formula

                        substituted_location_invariant_original_delay = substitute(substituted_location_invariant_original_delay,(update_key,update_formula))
                        location_invariant_update = substitute(update_formula,(self.delay,self.delay_1))
                        substituted_location_invariant = substitute(substituted_location_invariant,(update_key,location_invariant_update))
                        # print("Substituted location invariant update: ",location_invariant_update)
                        # print("Substituted location invariant after: ",substituted_location_invariant)
                        # print("Substituted location invariant with original delay: ",substituted_location_invariant_original_delay)
                    updated_location_invariant = And(substituted_location_invariant_original_delay,Not(And((self.delay_1>0),(self.delay_1<=self.delay),Not(substituted_location_invariant))))
                    # print("Location invariant: ",updated_location_invariant)
                    # print(updates)

                    # [self.primed_locations[self.current_locations[key]][i]==self.variable_mapping[self.original_vars[key]][i] for key in self.current_locations]

                    # for key in self.current_locations:
                    #     print(self.primed_locations[self.current_locations[key]][i]==self.location_mapping[self.original_locations[key]][i])

                    transition_cond = And([self.delay > 0]\
                                          +[self.primed_time[self.time][i] == self.time[i] + self.delay]\
                                          +[self.primed_time[self.time][i] > 0]\
                                          +[value for key,value in updates.items()]\
                                          +[updated_location_invariant]\
                                          +[self.primed_locations[self.current_locations[key]][i]==self.location_mapping[self.original_locations[key]][i] for key in self.current_locations]\
                                          +[unchanged]
                    )
                    
                    # print(transition_cond)
                    self.transitions.append(transition_cond)                    
                else:
                    print("Error in transition formula")
                    return None,None,None
        
        print("Initial condition: ",self.initial)
        counter=0
        for transition in self.transitions:
            counter=counter+1
            print("Transition ",counter)
            print(transition)


        #return the array variables,time and location 
        return self.current_variables,self.current_time,self.current_locations

    #invokes backward reachability algorithm 
    def check_reachability(self,unsafe_formula,num_quantifiers):
        print("Unsafe formula")
        print(unsafe_formula)
        safety = self.backward_reach.reachable(self.current_variables,self.current_locations,self.current_time,self.current_delay,self.current_intermediate_delay,self.initial,self.transitions,unsafe_formula,num_quantifiers)
        if safety==False:
            print("SYSTEM IS UNSAFE")
        else:
            print("SYSTEM IS SAFE !")
