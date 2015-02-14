from quipp import *

nfeatures = 10
FeaturesType = Vector(nfeatures, Bool)

get_class = rand_function(Unit, Bool)

class_1_features = rand_function(Unit, FeaturesType)
class_2_features = rand_function(Unit, FeaturesType)

def sample():
  which_class = get_class()
  if which_class:
    features = class_1_features()
  else:
    features = class_2_features()
  return (which_class, features)

run_example(sample)
