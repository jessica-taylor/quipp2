from quipp import *

dim = 2
nclusters = 3
PointType = Vector(dim, Double)
ClusterType = Categorical(nclusters)

get_cluster = rand_function(ClusterType)

get_point = rand_function(ClusterType, PointType)

def sample():
  # cluster = Uniform(nclusters)
  cluster = get_cluster()
  return (cluster, get_point(cluster))

run_example(sample)
