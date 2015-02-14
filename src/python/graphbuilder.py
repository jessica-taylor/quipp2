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
    self.randFuns = []
    self.factors = []
    self.varReplacements = {}

  def newVar(self, expfam):
    varid = len(self.vars)
    self.vars.append(expfam)
    return VarId(self, varid)

  def resolveVar(self, varid):
    if varid.id in self.varReplacements:
      return self.varReplacements[varid.id]
    else:
      return varid

  def unifyVars(self, a, b):
    def replace(v):
      return a if v == b else v

    def replaceInFactor(fac):
      (facInfo, args) = fac
      return (facInfo, map(replace, args))

    self.varReplacements[a.id] = b
    self.factors = map(replaceInFactor, self.factors)
    return a

  def unifyValues(self, typ, a, b):
    # TODO: this fails for e.g. Maybe
    avars = typ.embeddedVars(a)
    bvars = typ.embeddedVars(b)
    assert len(avars) == len(bvars)
    for av, bv in zip(avars, bvars):
      self.unifyVars(av, bv)
    return a

  def newFactor(self, facInfo, args):
    facid = len(self.factors)
    self.factors.append((facInfo, map(self.resolveVar, args)))
    return FactorId(self, facid)

  def newRandFun(self, argExpFams, resExpFam):
    rfid = len(self.randFuns)
    self.randFuns.append((argExpFams, resExpFam))
    return RandFunId(self, rfid)

  def newSampleFromRandFun(self, rfid, argVars):
    (argExpFams, resExpFam) = self.randFuns[rfid.id]
    assert len(argExpFams) == len(argVars)
    v = self.newVar(resExpFam)
    fac = self.newFactor(rfid, [v] + argVars)
    return v

  def newConstFactor(self, varid, value):
    varid = self.resolveVar(varid)
    ef = self.vars[varid]
    return newFactor({'type': 'constant', 'value': value})

  def newConstVar(self, ef, value):
    varid = self.newVar(ef)
    fac = self.newConstFactor(varid, value)
    return varid

  def randFunction(self, argTypes, resType):
    argTupleType = Tuple(argTypes)
    rfids = [self.newRandFun(argTupleType.expFams(), ef) for ef in resType.expFams()]
    def rf(*args):
      assert len(args) == len(argTypes)
      argVars = argTupleType.embeddedVars(tuple(args))
      resVars = [self.newSampleFromRandFun(rfid, argVars) for rfid in rfids]
      return resType.varsToValue(resVars)
    return rf

    

  def toJSON(self):
    return {
      'vars': self.vars,
      'randFuns': [{argExpFams: aefs, resExpFam: ref} for (aefs, ref) in self.randFuns],
      'factors': [{'factor': facinfo, 'argVarIds': args} for (facinfo, args) in self.factors]
    }

"""
Type interface:

t.expFams()
  Returns a list of exponential family names

t.embeddedVars(value)
  Returns a list of var ids in value

t.varsToValue(vars)
  Given a queue of var ids, create a value

t.unfreeze(state, value)
  Unfreezes a frozen value
"""

class DoubleValue(object):
  def __init__(self, varid):
    self.varid = varid

  def freeze(self, varvals):
    return varvals[self.varid]

class Double_class(object):

  def expFams(self):
    return ['gaussian']

  def embeddedVars(self, value):
    return [value.varid]

  def varsToValue(self, vars):
    return [DoubleValue(vars.get())]

  def unfreeze(self, state, value):
    return DoubleValue(state.newConstVar('gaussian', value))
    

Double = Double_class()

class Bool_class(object):

  def expFams(self):
    return ['bernoulli']

  def embeddedVars(self, value):
    return [value]

  def varsToValue(self, vars):
    return [vars.get()]

  def unfreeze(self, state, value):
    return BoolValue(state.newConstVar('bernoulli', value))

Bool = Bool_class()

class TupleValue(object):

  def __init__(self, fields):
    self.fields = tuple(fields)

  def freeze(self, varvals):
    return tuple([x.freeze(varvals) for x in self.fields])

class Tuple(object):

  def __init__(self, *types):
    self.types = types

  def expFams(self):
    ef = []
    for t in self.types:
      ef.extend(t.expFams())
    return ef

  def embeddedVars(self, value):
    vs = []
    for (t, v) in zip(self.types, value.fields):
      vs.extend(t.embeddedVars(v))
    return vs

  def varsToValue(self, vars):
    val = []
    for t in self.types:
      val.append(t.varsToValue(vars))
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

  def expFams(self):
    return ['bernoulli'] * (self.n - 1)

  def embeddedVars(self, value):
    return value.varids

  def varsToValue(self, vars):
    varids = []
    for i in range(self.n - 1):
      varids.append(vars.get())
    return CategoricalValue(varids)

  def unfreeze(self, state, value):
    return CategoricalValue([state.newConstVar('bernoulli', value == i) for i in range(self.n - 1)])


def Vector(n, typ):
  return Tuple(*([typ]*n))

currentGraphState = GraphState()

def randFunction(t1, t2):
  return currentGraphState.randFunction(t1, t2)

def conditioned_network(state, typ, sampler, frozenSamps):
  samples = [sampler() for i in range(len(samps))]
  for (latent, s), fs in zip(samples, frozenSamps):
    unfrozen = typ.unfreeze(fs)
    state.unifyValues(s, unfrozen)
  return [latent for (latent, _) in samples]


def run_example(sampler):
  n = 10
  samples = [sample() for i in range(n)]

