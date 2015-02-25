from quipp import *

num_states = 5
num_observations = 3

StateType = Categorical(num_states)
ObsType = Categorical(num_observations)

trans_fun = rand_function(StateType, StateType)
obs_fun = rand_function(StateType, ObsType)

def sample():
  states = [uniform(num_states)]
  for i in range(9):
    states.append(trans_fun(states[-1]))
  return (states, [obs_fun(s) for s in states])

run_example(sample)
