"""Exact point counts for the four finite models in the exceptional-component test."""
import json

p = 19
legendre = [0]*p
for x in range(1,p):
    legendre[x] = 1 if pow(x, (p-1)//2, p) == 1 else -1

def count(f):
    table = [legendre[f(x) % p] for x in range(p)]
    return p + 1 + sum(table), table

beta = 17*2 % p
k = (1-324*beta)*(1-2916*beta) % p
assert (beta,k) == (15,14)
assert pow(2,9,19) == 18
assert pow(-3,9,19) == 1
n0, cm = count(lambda x: x*x*x-x)
assert n0 == 20 and all(cm[x] == -cm[-x % p] for x in range(p))
rows = {}
for label, m in [('beta',beta),('minus3beta',-3*beta%p),('beta_k',beta*k%p)]:
    assert m
    n, cs = count(lambda x: x*(x-m)*(x+3*m))
    rows[label] = {'m_mod_19':m,'count':n,'trace':p+1-n,'legendre_by_x':cs}
assert [(a['m_mod_19'],a['count'],a['trace']) for a in rows.values()] == [(15,16,4),(12,16,4),(1,24,-4)]
print(json.dumps(dict(p=p,geometric_source_reference={'count':n0,'trace':0,'legendre_by_x':cm},
                      targets=rows,
                      scope='Finite models only; no actual exceptional component or global rational point.'),
                 indent=2))
