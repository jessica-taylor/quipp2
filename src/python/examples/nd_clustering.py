from quipp import *

dim = 2
nclusters = 3
PointType = Vector(dim, Double)
ClusterType = Categorical(nclusters)

get_point = rand_function(ClusterType, PointType)

def sample():
  cluster = UniformCategorical(nclusters)
  return (cluster, get_point(cluster))

run_example(sample)
