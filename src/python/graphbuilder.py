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
    def replace(v):
      return a if v == b else v

    def replace_in_factor(fac):
      (fac_info, args) = fac
      return (fac_info, map(replace, args))

    self.var_replacements[b.id] = a
    del self.vars[b.id]
    self.factors = map(replace_in_factor, self.factors)
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
    return {
      'vars': [[varid, expfam] for (varid, expfam) in self.vars.items()],
      'randFuns': [{'argExpFams': aefs, 'resExpFam': ref} for (aefs, ref) in self.rand_funs],
      'factors': [{'factor': facinfo, 'argVarIds': [a.id for a in args]} for (facinfo, args) in self.factors]
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
    return varvals[self.varid.id]

gaussian_exp_fam = {'type': 'gaussian'}
bernoulli = {'type': 'bernoulli'}
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
    return DoubleValue(state.new_const_var('gaussian', value))

  def __repr__(self):
    return 'Double'

Double = DoubleClass()

class BoolValue(object):
  def __init__(self, varid):
    self.varid = varid

  def get_type(self):
    return Bool

  def freeze(self, varvals):
    return varvals[self.varid.id]

class BoolClass(object):

  def exp_fams(self):
    return [bernoulli_exp_fam]

  def embedded_vars(self, value):
    return [value.varid]

  def vars_to_value(self, vars):
    return BoolValue(vars.dequeue())

  def unfreeze(self, state, value):
    return BoolValue(state.new_const_var('bernoulli', value))

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

  def __init__(self, varids):
    self.varids = varids

  def get_type(self):
    return Categorical(len(self.varids) + 1)

  def freeze(self, varvals):
    i = 0
    for varid in self.varids:
      if varvals[varid.id]:
        return i
      i += 1
    return i

class Categorical(object):

  def __init__(self, n):
    self.n = n

  def exp_fams(self):
    return ['bernoulli'] * (self.n - 1)

  def embedded_vars(self, value):
    return value.varids

  def vars_to_value(self, vars):
    varids = []
    for i in range(self.n - 1):
      varids.append(vars.dequeue())
    return CategoricalValue(varids)

  def unfreeze(self, state, value):
    return CategoricalValue([state.new_const_var('bernoulli', value == i) for i in range(self.n - 1)])

  def __repr__(self):
    return 'Categorical(' + str(self.n) + ')'

def get_type(value):
  if hasattr(value, 'get_type'):
    return value.get_type()
  elif isinstance(value, tuple):
    return Tuple(*map(get_type, value))
  else:
    raise Exception('Unknown value type ' + str(type(value)) + ', value ' + str(value))

def freeze_value(value, varvals):
  if hasattr(value, 'freeze'):
    return value.freeze(varvals)
  elif isinstance(value, tuple):
    return tuple([freeze_value(v, varvals) for v in value])
  else:
    raise Exception('Unknown value type ' + str(type(value)) + ', value ' + str(value))

def Vector(n, typ):
  return Tuple(*([typ]*n))

Unit = Tuple()

current_graph_state = GraphState()

def rand_function(*ts):
  return current_graph_state.rand_function(ts[:-1], ts[-1])

def conditioned_network(state, typ, sampler, frozen_samps):
  samples = [sampler() for i in range(len(samps))]
  for (latent, s), fs in zip(samples, frozen_samps):
    unfrozen = typ.unfreeze(fs)
    state.unify_values(get_type(s), s, unfrozen)
  return [latent for (latent, _) in samples]

def infer_parameters_from_samples(graph_state, samples, frozen_samples):
  for s,f in zip(samples, frozen_samples):
    typ = get_type(s)
    graph_state.unify_values(typ, s, typ.unfreeze(graph_state, f))
  templ = graph_state.to_JSON()
  (state, params) = hs_init_em(templ)
  state_params_list = [(state, params)]
  for i in range(10):
    (state, params) = hs_step_em(templ, state, params)
    state_params_list.append((state, params))
  return state_params_list

def run_example(sampler):
  n = 1000
  samples = [sampler() for i in range(n)]
  templ = current_graph_state.to_JSON()
  rand_params = hs_rand_template_params(templ)
  varvals = state_to_varvals(hs_sample_bayes_net(templ, rand_params))
  frozen_samples = [freeze_value(samp, varvals) for samp in samples]
  state_params_list = infer_parameters_from_samples(current_graph_state, samples, frozen_samples)
  print rand_params
  print state_params_list[-1][1]
