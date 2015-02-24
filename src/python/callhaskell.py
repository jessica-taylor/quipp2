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


def temp_file_name(prefix=''):
    return '/tmp/' + prefix + '_' + str(uuid.uuid1())

def run_hs(*args):
    subprocess.call(['../../dist/build/quipp_main/quipp_main'] + list(args))

def dump_template(templ):
    templ_file = temp_file_name('template')
    json.dump(templ, open(templ_file, 'w'))
    return templ_file

def dump_state(state):
    state_file = temp_file_name('state')
    json.dump(state, open(state_file, 'w'))
    return state_file

def dump_params(params):
    params_file = temp_file_name('params')
    json.dump(params, open(params_file, 'w'))
    return params_file

def load_contents(fname):
  return json.load(open(fname))

def hs_rand_template_params(templ):
    params_file = temp_file_name('params')
    run_hs('randTemplateParams', dump_template(templ), params_file)
    return load_contents(params_file)

def hs_sample_bayes_net(templ, params):
    state_file = temp_file_name('state')
    run_hs('sampleBayesNet', dump_template(templ), dump_params(params), state_file)
    return load_contents(state_file)

def hs_init_em(templ):
    state_file = temp_file_name('state')
    params_file = temp_file_name('params')
    run_hs('initEM', dump_template(templ), state_file, params_file)
    return (load_contents(state_file), load_contents(params_file))

def hs_step_em(templ, state, params):
    state_file = dump_state(state)
    params_file = dump_params(params)
    run_hs('stepEM', dump_template(templ), state_file, params_file)
    return (load_contents(state_file), load_contents(params_file))

__all__ = ['hs_rand_template_params', 'hs_sample_bayes_net', 'hs_init_em', 'hs_step_em', 'state_to_varvals', 'varvals_to_state']

if __name__ == '__main__':
    print hs_init_em({'vars': [], 'randFuns': [], 'factors': []})
