import math
import numpy as np
from numpy import linalg
import itertools
from callhaskell import *

class Queue(object):

  def __init__(self, items=None):
    if items is None:
      self.items = []
    else:
      self.items = list(reversed(items))

  def dequeue(self):
    return self.items.pop()


class VarId(object):
  def __init__(self, state, id, expfam):
    assert isinstance(id, int)
    self.state = state
    self.id = id
    self.expfam = expfam

class FactorId(object):
  def __init__(self, state, id):
    assert isinstance(id, int)
    self.state = state
    self.id = id

class RandFunId(object):
  def __init__(self, state, id):
    assert isinstance(id, int)
    self.state = state
    self.id = id

class GraphState(object):

  def __init__(self):
    self.vars = {}
    self.var_count = 0
    self.rand_funs = []
    self.factors = []
    self.var_replacements = {}

  def new_var(self, expfam):
    varid = self.var_count
    self.var_count += 1
    self.vars[varid] = expfam
    return VarId(self, varid, expfam)

  def resolve_var(self, varid):
    if varid.id in self.var_replacements:
      return self.var_replacements[varid.id]
    else:
      return varid

  def unify_vars(self, a, b):
    self.var_replacements[b.id] = a
    del self.vars[b.id]
    return a

  def unify_values(self, typ, a, b):
    # TODO: this fails for e.g. Maybe
    avars = typ.embedded_vars(a)
    bvars = typ.embedded_vars(b)
    assert len(avars) == len(bvars)
    for av, bv in zip(avars, bvars):
      self.unify_vars(av, bv)
    return a

  def new_factor(self, fac_info, args):
    facid = len(self.factors)
    self.factors.append((fac_info, map(self.resolve_var, args)))
    return FactorId(self, facid)

  def new_rand_fun(self, arg_exp_fams, res_exp_fam):
    rfid = len(self.rand_funs)
    self.rand_funs.append((arg_exp_fams, res_exp_fam))
    return RandFunId(self, rfid)

  def new_sample_from_rand_fun(self, rfid, arg_vars):
    (arg_exp_fams, res_exp_fam) = self.rand_funs[rfid.id]
    assert len(arg_exp_fams) == len(arg_vars)
    v = self.new_var(res_exp_fam)
    fac = self.new_factor({'type': 'randFun', 'id': rfid.id}, [v] + arg_vars)
    return v

  def new_const_factor(self, varid, value):
    varid = self.resolve_var(varid)
    ef = self.vars[varid.id]
    return self.new_factor({'type': 'constant', 'expFam': ef, 'value': value}, [varid])

  def new_const_var(self, ef, value):
    varid = self.new_var(ef)
    fac = self.new_const_factor(varid, value)
    return varid

  def rand_function(self, arg_types, res_type):
    arg_tuple_type = Tuple(*arg_types)
    rfids = [self.new_rand_fun(arg_tuple_type.exp_fams(), ef) for ef in res_type.exp_fams()]
    def rf(*args):
      assert len(args) == len(arg_types)
      arg_vars = arg_tuple_type.embedded_vars(tuple(args))
      res_vars = [self.new_sample_from_rand_fun(rfid, arg_vars) for rfid in rfids]
      return res_type.vars_to_value(Queue(res_vars))
    return rf

  def to_JSON(self):
    def replace_id(varid):
      if varid.id in self.var_replacements:
        return self.var_replacements[varid.id].id
      else:
        return varid.id
    return {
      'vars': [[varid, expfam] for (varid, expfam) in self.vars.items()],
      'randFuns': [{'argExpFams': aefs, 'resExpFam': ref} for (aefs, ref) in self.rand_funs],
      'factors': [{'factor': facinfo, 'argVarIds': [replace_id(a) for a in args]} for (facinfo, args) in self.factors]
    }

"""
Type interface:

t.exp_fams()
  Returns a list of exponential family names

t.embedded_vars(value)
  Returns a list of var ids in value

t.vars_to_value(vars)
  Given a queue of var ids, create a value

t.unfreeze(state, value)
  Unfreezes a frozen value
"""

class DoubleValue(object):
  def __init__(self, varid):
    self.varid = varid

  def get_type(self):
    return Double

  def freeze(self, varvals):
    return varvals[self.varid.id]['value']

gaussian_exp_fam = {'type': 'gaussian'}
bernoulli_exp_fam = {'type': 'bernoulli'}
def categorical_exp_fam(n):
  return {'type': 'categorical', 'n': n}

class DoubleClass(object):

  def exp_fams(self):
    return [gaussian_exp_fam]

  def embedded_vars(self, value):
    return [value.varid]

  def vars_to_value(self, vars):
    return DoubleValue(vars.dequeue())

  def unfreeze(self, state, value):
    return DoubleValue(state.new_const_var(gaussian_exp_fam, value))

  def __repr__(self):
    return 'Double'

Double = DoubleClass()

class BoolValue(object):
  def __init__(self, varid):
    self.varid = varid

  def get_type(self):
    return Bool

  def freeze(self, varvals):
    return varvals[self.varid.id]['value']

class BoolClass(object):

  def exp_fams(self):
    return [bernoulli_exp_fam]

  def embedded_vars(self, value):
    return [value.varid]

  def vars_to_value(self, vars):
    return BoolValue(vars.dequeue())

  def unfreeze(self, state, value):
    return BoolValue(state.new_const_var(bernoulli_exp_fam, value))

  def __repr__(self):
    return 'Bool'

Bool = BoolClass()

# class TupleValue(object):
# 
#   def __init__(self, fields):
#     self.fields = tuple(fields)

class Tuple(object):

  def __init__(self, *types):
    self.types = types

  def exp_fams(self):
    ef = []
    for t in self.types:
      ef.extend(t.exp_fams())
    return ef

  def embedded_vars(self, value):
    vs = []
    for (t, v) in zip(self.types, value):
      vs.extend(t.embedded_vars(v))
    return vs

  def vars_to_value(self, vars):
    val = []
    for t in self.types:
      val.append(t.vars_to_value(vars))
    return tuple(val)

  def freeze(self, varvals, value):
    return tuple([t.freeze(varvals, x) for (t, x) in zip(self.types, value)])

  def unfreeze(self, state, value):
    return tuple([t.unfreeze(state, v) for (t, v) in zip(self.types, value)])

  def __repr__(self):
    return repr(self.types)

class CategoricalValue(object):

  def __init__(self, varid, n):
    self.varid = varid
    self.n = n

  def get_type(self):
    return Categorical(self.n)

  def freeze(self, varvals):
    return varvals[self.varid.id]['value']

class Categorical(object):

  def __init__(self, n):
    self.n = n

  def exp_fams(self):
    return [categorical_exp_fam(self.n)]

  def embedded_vars(self, value):
    return [value.varid]

  def vars_to_value(self, vars):
    return CategoricalValue(vars.dequeue(), self.n)

  def unfreeze(self, state, value):
    return CategoricalValue(state.new_const_var(categorical_exp_fam(self.n), value), self.n)

  def __repr__(self):
    return 'Categorical(' + str(self.n) + ')'

def get_type(value):
  if hasattr(value, 'get_type'):
    return value.get_type()
  elif isinstance(value, (tuple, list)):
    return Tuple(*map(get_type, value))
  else:
    raise Exception('Unknown value type ' + str(type(value)) + ', value ' + str(value))

def freeze_value(value, varvals):
  if hasattr(value, 'freeze'):
    return value.freeze(varvals)
  elif isinstance(value, (tuple, list)):
    return tuple([freeze_value(v, varvals) for v in value])
  else:
    raise Exception('Unknown value type ' + str(type(value)) + ', value ' + str(value))

def Vector(n, typ):
  print 'vector', n, typ, Tuple(*([typ]*n))
  return Tuple(*([typ]*n))

Unit = Tuple()

current_graph_state = GraphState()

def rand_function(*ts):
  return current_graph_state.rand_function(ts[:-1], ts[-1])

def uniform_categorical(n):
  v = current_graph_state.new_var(categorical_exp_fam(n))
  current_graph_state.new_factor({'type': 'uniformCategorical', 'n': n}, [v])
  return CategoricalValue(v, n)

def normal(mean, stdev):
  v = current_graph_state.new_var(gaussian_exp_fam)
  current_graph_state.new_factor({'type': 'normal', 'mean': mean, 'stdev': stdev}, [v])
  return DoubleValue(v)


def conditioned_network(state, typ, sampler, frozen_samps):
  samples = [sampler() for i in range(len(samps))]
  for (latent, s), fs in zip(samples, frozen_samps):
    unfrozen = typ.unfreeze(fs)
    state.unify_values(get_type(s), s, unfrozen)
  return [latent for (latent, _) in samples]

def infer_parameters_from_samples(graph_state, samples, frozen_samples):
  for s,f in zip(samples, frozen_samples):
    typ = get_type(s[1])
    graph_state.unify_values(typ, s[1], typ.unfreeze(graph_state, f))
  templ = graph_state.to_JSON()
  (state, params) = hs_init_em(templ)
  yield (state, params)
  i = 0
  while True:
    print 'iter', i
    (state, params) = hs_step_em(templ, state, params)
    yield (state, params)
    i += 1

def translate_params_for_fn(params):
  if len(params[1][0]) == 0:
    probs = [math.exp(x) for x in [0.0] + params[0]]
    sum_probs = sum(probs)
    return [p/sum_probs for p in probs]
  else:
    variance = -1.0 / (2 * params[0][1])
    factors = [params[0][0]] + params[1][0]
    return (variance, [f*variance for f in factors])

def params_to_cluster_centers(params):
  d = dict(params)
  cluster_centers = []
  for i in d:
    ps = d[i]
    variance = -1.0 / (2 * ps[0][1])
    factors = [ps[0][0]] + ps[1][0]
    scaled_factors = [f*variance for f in factors]
    centers = [scaled_factors[0]] + [x + scaled_factors[0] for x in scaled_factors[1:]]
    cluster_centers.append(centers)
  return zip(*cluster_centers)

def cluster_centers_error(cs1, cs2):
  errs = []
  def tup_dist(t1, t2):
    return sum((a-b)**2 for (a, b) in zip(t1, t2))
  for cs in itertools.permutations(cs1):
    errs.append(sum(map(tup_dist, cs, cs2)))
  return min(errs)

def cluster_assignment_accuracy(cs1, cs2):
  accuracies = []
  for perm in itertools.permutations(range(3)):
    accuracies.append(float(len([() for (a, b) in zip(cs1, cs2) if a == perm[b]])) / len(cs1))
  return max(accuracies)



def translate_params(params):
  return [(x, translate_params_for_fn(y)) for (x, y) in params]


def mean(xs):
  return sum(xs) / len(xs)

def run_clustering_example(run):
  global current_graph_state
  n = 100
  accs = []
  for i in range(100):
    current_graph_state = GraphState()
    sampler = run()
    samples = [sampler() for i in range(n)]
    templ = current_graph_state.to_JSON()
    rand_params = hs_rand_template_params(templ)
    varvals = state_to_varvals(hs_sample_bayes_net(templ, rand_params))
    frozen_samples = [freeze_value(samp, varvals) for samp in samples]
    true_latents = [x[0] for x in frozen_samples]
    print true_latents
    state_params_list = infer_parameters_from_samples(current_graph_state, samples, [x[1] for x in frozen_samples])
    rand_cs = params_to_cluster_centers(rand_params)
    iter_accs = []
    j = 0
    for (state, params) in state_params_list:
      cs = params_to_cluster_centers(params)
      if j > 1:
        varvals = state_to_varvals(state)
        state_latents = [freeze_value(samp[0], varvals) for samp in samples]
        acc = cluster_assignment_accuracy(true_latents, state_latents)
        iter_accs.append(acc)
      j += 1
    accs.append(iter_accs)
  print map(mean, zip(*accs))


def params_to_matrix(params):
  coords = []
  component_variances = []
  for (i, ((base_n1, n2), (lin,))) in params:
    component_variances.append(-1.0 / (2 * n2))
    coords.append([-l/(2 * n2) for l in [base_n1] + lin])
  return component_variances, np.matrix(coords)

def matrix_to_gaussian(variances_mat):
  variances, mat = variances_mat
  mean = mat[:,0]
  a = mat[:, 1:]
  return (mean, a * a.T + np.diag(variances))

def gaussian_kl(p, q):
  (pm, pv) = p
  (qm, qv) = q
  n = pm.shape[0]
  assert pv.shape[0] == n == qv.shape[0]
  return 0.5 * (np.trace(linalg.inv(qv) * pv) + ((qm - pm).T * linalg.inv(qv) * (qm - pm)).item((0,0)) - n + linalg.slogdet(qv)[1] - linalg.slogdet(pv)[1])

def rotation_invariant_dist(A, B):
  # min_R ||AR - B||^2
  # = min_R tr((AR - B)^T(AR - B))
  # = min_R tr(R^TA^T A R - B^T A R - R^T A^T B + B^T B)
  # = ||A||^2 + ||B||^2 - 2 max_R tr(R^T A^T B)
  #
  # A^T B = USV^T
  #
  # = ||A||^2 + ||B||^2 - 2 max_R tr(R^T USV^T)
  # = ||A||^2 + ||B||^2 - 2 max_R tr(V^T R^T US)
  # = ||A||^2 + ||B||^2 - 2 max_R tr(S)
  # -> R = UV^T

  u, s, v = linalg.svd(A.T * B)
  r = u * v
  # print linalg.norm(A*r - B)**2
  return (r, linalg.norm(A)**2 + linalg.norm(B)**2 - 2 * sum(s))
  

# IDEA: compute Gaussian from factors, KL divergence!

def run_factor_analysis_example(run):
  global current_graph_state
  n = 200
  accs = []
  for i in range(1):
    current_graph_state = GraphState()
    sampler = run()
    samples = [sampler() for i in range(n)]
    templ = current_graph_state.to_JSON()
    rand_params = hs_rand_template_params(templ)
    rand_mat = params_to_matrix(rand_params)
    print rand_mat
    varvals = state_to_varvals(hs_sample_bayes_net(templ, rand_params))
    frozen_samples = [freeze_value(samp, varvals) for samp in samples]
    true_latents = [x[0] for x in frozen_samples]
    # print true_latents
    state_params_list = infer_parameters_from_samples(current_graph_state, samples, [x[1] for x in frozen_samples])
    # rand_cs = params_to_cluster_centers(rand_params)
    iter_accs = []
    j = 0
    prev_state_latents = None
    for (state, params) in state_params_list:
      guess_mat = params_to_matrix(params)
      # cs = params_to_cluster_centers(params)
      if j > 1:
        print guess_mat
        print 'kl', gaussian_kl(matrix_to_gaussian(rand_mat), matrix_to_gaussian(guess_mat))
        varvals = state_to_varvals(state)
        state_latents = [freeze_value(samp[0], varvals) for samp in samples]
        if prev_state_latents:
          count_diffs = float(len([s for (s, s2) in zip(state_latents, prev_state_latents) if s != s2])) / len(state_latents)
          print count_diffs
        # print state_latents
        prev_state_latents = state_latents
        # acc = cluster_assignment_accuracy(true_latents, state_latents)
        # iter_accs.append(acc)
      j += 1

    # accs.append(iter_accs)
  # print map(mean, zip(*accs))
