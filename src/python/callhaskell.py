import json
import uuid
import subprocess


"""
Utilities for calling the Haskell code.

JSON:

expfam:
  'gaussian', 'bernoulli'

template:
    {vars: [expfam],
     randFuns: [
       {argExpFams: [expfam],
        resExpFam: expfam
       }
     ],
     factors: [
       {factor:
        argVarIds: [int],
        {type: 'randFun', randFunId: int}
        ||
        {type: 'constant', value: *}}
     ]
    }

    This only has to be encoded by Python and decoded by Haskell!

params:
  {<int>: {
    base: [double],
    matrix: [[double]]
  }

  Python does not need to know anything about this.

state:
  {<int>: *}

  Both Python and Haskell must know about this.

pyRandTemplateParams(templ)
  generate random parameters for a given template

pySampleBayesNet(templ, params)
  given template and parameters, return a sample map of varids to value

pyInitEM(templ)
  generate [state, params]

pyStepEM(templ, state, params)
  return [newState, newParams]
"""

def state_to_varvals(state):
  m = {}
  for (v, s) in state:
    m[v] = s[u'Left']
  return m

def varvals_to_state(varvals):
  s = []
  for k in varvals:
    s.append([k, {u'Left': varvals[k]}])

def run_hs(command, *args):
    popen = subprocess.Popen(['../../dist/build/quipp_main/quipp_main', command], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    (output, _) = popen.communicate(json.dumps(list(args)))
    return json.loads(output)

def hs_rand_template_params(templ):
  return run_hs('randTemplateParams', templ)

def hs_sample_bayes_net(templ, params):
  return run_hs('sampleBayesNet', templ, params)

def hs_init_em(templ):
  return run_hs('initEM', templ)

def hs_infer_state(templ, state, params, iters=10):
  return run_hs('inferState', templ, state, params, iters)

def hs_infer_params(templ, state, params):
  return run_hs('inferParams', templ, state, params)

# def hs_step_em(templ, state, params):
#   return run_hs('stepEM', templ, state, params)

def hs_score(templ, state, params):
  return run_hs('score', templ, state, params)

# __all__ = ['hs_rand_template_params', 'hs_sample_bayes_net', 'hs_init_em', 'hs_step_em', 'state_to_varvals', 'varvals_to_state']

if __name__ == '__main__':
    print hs_init_em({'vars': [], 'randFuns': [], 'factors': []})
