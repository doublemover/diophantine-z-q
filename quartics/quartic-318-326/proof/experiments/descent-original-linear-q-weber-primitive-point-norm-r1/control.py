"""Check the literal orbit and primitive positive norm on actual E(F_q)."""
from itertools import product
from math import isqrt
def prime(q):
    return q > 1 and all(q%d for d in range(2,isqrt(q)+1))
def add(P,Q,p):
    if P is None: return Q
    if Q is None: return P
    x,y=P; z,w=Q
    if x==z:
        if (y+w)%p==0: return None
        s=(3*x*x-1)*pow(2*y,-1,p)%p
    else:
        s=(y-w)*pow(x-z,-1,p)%p
    X=(s*s-x-z)%p
    return X, (-y-s*(X-x))%p
def neg(P,p):
    return None if P is None else (P[0],-P[1]%p)
def turn(P,i,p):
    return None if P is None else (-P[0]%p,i*P[1]%p)
def W(P,p):
    return None if P is None else P[0]**2%p
pairs=unit_checks=primitive=scalar_checks=0
for p in range(5,312,4):
  if not prime(p): continue
  J=[i for i in range(p) if (i*i+1)%p==0]
  E=[None]+[(x,y) for x,y in product(range(p),repeat=2) if (y*y-x*x*x+x)%p==0]
  for i in J:
    bins={v:{Q for Q in E if W(Q,p)==v} for v in {W(P,p) for P in E}}
    for P in E:
      I=turn(P,i,p)
      orbit={P,neg(P,p),I,neg(I,p)}
      assert bins[W(P,p)]==orbit
      pairs+=len(E)
      ps=[None]; qs=[None]
      for _ in range(8):
        ps.append(add(ps[-1],P,p))
        qs.append(add(qs[-1],I,p))
      for M in range(2,9,2):
        if ps[M] is not None or qs[M] is not None: continue
        T={(a,b):add(ps[a],qs[b],p) for a,b in product(range(M),repeat=2)}
        if len(set(T.values()))!=M*M: continue
        primitive+=1
        for a,b in product(range(-M,2*M),repeat=2):
          Q=T[a%M,b%M]
          scalar_checks+=1
          if W(Q,p)==W(P,p):
            u=[(c,d) for c,d in [(1,0),(-1,0),(0,1),(0,-1)]
               if (a-c)%M==0 and (b-d)%M==0]
            assert u and (a*a+b*b-1)%(2*M)==0
            unit_checks+=1
print(f"actual stock-point pair orbit tests: {pairs}")
print(f"actual primitive point/level/root triples: {primitive}")
print(f"actual scalar tests: {scalar_checks}; same-value tests: {unit_checks}")
assert min(primitive,unit_checks)>0
