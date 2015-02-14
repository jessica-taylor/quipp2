from quipp import *

num_components = 3
point_dim = 5

ComponentsType = Vector(num_components, Double)
PointType = Vector(point_dim, Double)

get_point = randFunction(ComponentsType, PointType)

def sample():
  components = [normal(0, 1) for i in range(num_components)]
  return (comenents, get_point(components))

run_example(sample)
