"""Exact fixed-beta CF cycles; 15 visible orientation switches; no prime search."""
from math import isqrt, prod
from pathlib import Path
import json

base = Path(__file__).resolve().parent.parent
beta = prod((5,11,17,163,661,733,1489,1861))
R = 4376874610839020
M = 1+114444*R
S = isqrt(beta)
assert S*S < beta < (S+1)**2
small = json.loads((base/'rc-linked-scalar-specialization-r1/ACTUAL-THETA-MODULAR-ROWS.json').read_text())
large = json.loads((base/'rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json').read_text())
assert len(small)==1 and small[0]['prime']==6551
assert [r['prime'] for r in large] == [2470991,16782959]
W_rows = {131:1, 6551:small[0]['W'],
          **{r['prime']:r['W_mod_p_squared']%r['prime'] for r in large}}

def lift(p, w):
  c = 12*w*pow(M,-1,p)%p
  t = pow(c,-1,p)
  assert (beta-t*t)%p == 0
  T = t+p*(((beta-t*t)//p)*pow(2*t,-1,p)%p)
  assert 0 <= T < p*p and T*c%p==1 and (beta-T*T)%(p*p)==0
  return [p,w,c,t,T]

rows = [lift(p,w) for p,w in W_rows.items()]
primes = list(W_rows)

def nxt(st):
  p,q = st
  assert q != 0
  a = (p+S+int(q<0))//q
  P = a*q-p
  Q,rem = divmod(beta-P*P,q)
  assert Q != 0 and rem == 0
  return P,Q

def orbit(initial, avoid=()):
  seen = {}
  s = initial
  while s not in seen:
    assert s not in avoid
    assert len(seen) < 300000
    seen[s] = len(seen)
    s = nxt(s)
  return seen,s

principal, repeat = orbit((0,1))
assert len(principal)==265347 and principal[repeat]==1
out = []
for mask in range(1,16):
  d = 1
  P = 0
  for j, (p,w,c,t,T) in enumerate(rows):
    if mask>>j&1:
      P += d*d*((T-P)*pow(d*d,-1,p*p)%(p*p))
      d *= p
  assert 0 <= P < d*d and (beta-P*P)%(d*d)==0
  seen, repeated = orbit((P,d*d), principal)
  out.append({'mask':mask, 'd':d, 'start':[P,d*d], 'visited':len(seen),
              'repeat_index':seen[repeated], 'repeat':repeated,
              'principal_intersection':False})
print(json.dumps({'beta':beta, 'M':M, 'sqrt_floor':S, 'primes':primes,
 'oriented_roots_p_W_cmodp_tmodp_tliftmodp2':rows,
 'principal':{'start':[0,1],'visited':len(principal),'repeat_index':principal[repeat],'repeat':repeat},
 'switches':out},indent=2))
