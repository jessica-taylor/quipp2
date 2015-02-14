from quipp import *

input_dim = 100
hidden_dim = 20
output_dim = 2

InputType = Categorical(input_dim)
HiddenType = Categorical(hidden_dim)
OutputType = Categorical(output_dim)

input_to_hidden = rand_function(InputType, HiddenType)
hidden_to_output = rand_function(HiddenType, OutputType)

def sample(input_layer):
  hidden_layer = input_to_hidden(input_layer)
  output_layer = hidden_to_output(hidden_layer)
  return ((), output_layer)

run_example(sample)
