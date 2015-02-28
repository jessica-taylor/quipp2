from quipp import *

def run():
  num_components = 2
  point_dim = 5

  ComponentsType = Vector(num_components, Double)
  PointType = Vector(point_dim, Double)

  get_point = rand_function(ComponentsType, PointType)

  def sample():
    components = [normal(0, 1) for i in range(num_components)]
    return (components, get_point(components))

  return sample

run_example(run)
