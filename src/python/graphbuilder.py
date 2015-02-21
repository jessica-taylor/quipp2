import Queue


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
    self.vars = []
    self.rand_funs = []
    self.factors = []
    self.var_replacements = {}

  def new_var(self, expfam):
    varid = len(self.vars)
    self.vars.append(expfam)
    return VarId(self, varid)

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

    self.var_replacements[a.id] = b
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
    ef = self.vars[varid]
    return new_factor({'type': 'constant', 'value': value})

  def new_const_var(self, ef, value):
    varid = self.new_var(ef)
    fac = self.new_const_factor(varid, value)
    return varid

  def rand_function(self, arg_types, res_type):
    arg_tuple_type = Tuple(arg_types)
    rfids = [self.new_rand_fun(arg_tuple_type.exp_fams(), ef) for ef in res_type.exp_fams()]
    def rf(*args):
      assert len(args) == len(arg_types)
      arg_vars = arg_tuple_type.embedded_vars(tuple(args))
      res_vars = [self.new_sample_from_rand_fun(rfid, arg_vars) for rfid in rfids]
      return res_type.vars_to_value(res_vars)
    return rf

  def to_jSON(self):
    return {
      'vars': self.vars,
      'rand_funs': [{arg_exp_fams: aefs, res_exp_fam: ref} for (aefs, ref) in self.rand_funs],
      'factors': [{'factor': facinfo, 'argVarIds': args} for (facinfo, args) in self.factors]
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

  def freeze(self, varvals):
    return varvals[self.varid]

class DoubleClass(object):

  def exp_fams(self):
    return ['gaussian']

  def embedded_vars(self, value):
    return [value.varid]

  def vars_to_value(self, vars):
    return [DoubleValue(vars.get())]

  def unfreeze(self, state, value):
    return DoubleValue(state.new_const_var('gaussian', value))
    

Double = DoubleClass()

class Bool_class(object):

  def exp_fams(self):
    return ['bernoulli']

  def embedded_vars(self, value):
    return [value]

  def vars_to_value(self, vars):
    return [vars.get()]

  def unfreeze(self, state, value):
    return Bool_value(state.new_const_var('bernoulli', value))

Bool = Bool_class()

class TupleValue(object):

  def __init__(self, fields):
    self.fields = tuple(fields)

  def freeze(self, varvals):
    return tuple([x.freeze(varvals) for x in self.fields])

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
    for (t, v) in zip(self.types, value.fields):
      vs.extend(t.embedded_vars(v))
    return vs

  def vars_to_value(self, vars):
    val = []
    for t in self.types:
      val.append(t.vars_to_value(vars))
    return TupleValue(val)

  def unfreeze(self, state, value):
    return TupleValue([t.unfreeze(state, v) for (t, v) in zip(self.types, value)])

class CategoricalValue(object):

  def __init__(self, varids):
    self.varids = varids

  def freeze(self, varvals):
    i = 0
    for varid in self.varids:
      if varvals[varid]:
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
      varids.append(vars.get())
    return CategoricalValue(varids)

  def unfreeze(self, state, value):
    return CategoricalValue([state.new_const_var('bernoulli', value == i) for i in range(self.n - 1)])


def Vector(n, typ):
  return Tuple(*([typ]*n))

current_graph_state = GraphState()

def rand_function(t1, t2):
  return current_graph_state.rand_function(t1, t2)

def conditioned_network(state, typ, sampler, frozen_samps):
  samples = [sampler() for i in range(len(samps))]
  for (latent, s), fs in zip(samples, frozen_samps):
    unfrozen = typ.unfreeze(fs)
    state.unify_values(s, unfrozen)
  return [latent for (latent, _) in samples]


def run_example(sampler):
  n = 10
  samples = [sample() for i in range(n)]

