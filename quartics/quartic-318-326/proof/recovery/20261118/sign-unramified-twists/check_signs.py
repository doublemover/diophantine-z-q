"""Exact functional identities and all sixteen reductions, not a scheme/descent proof."""
from itertools import product
def f(e,z):
 s,a,b,c=e;u,h,k,w=z
 return s*u, a*h+(a-s)//2*u, b*k+(b-s)//2*u,c*w+(c-s)*u+c-1
def g(e,z):
 s,a,b,c=e;a*=s;b*=s;c*=s;x,h,k,w=z
 return s*x,a*h+(a-1)//2,b*k+(b-1)//2,c*w+(c-s)*x+c-1
sg=list(product((1,-1),repeat=4))
for e in sg:
 for z in [(5,3,-7,13),(-2,9,5,-3)]:
  u,h,k,w=z;a,b,c,d=e
  U,H,K,W=f(e,z)
  assert (U,U+2*H,U+2*K,U+1+W)==(a*u,b*(u+2*h),c*(u+2*k),d*(u+1+w))
  X,H,K,W=g(e,z)
  assert (X,1+2*H,1+2*K,1+X+W)==(a*u,a*b*(1+2*h),a*c*(1+2*k),a*d*(1+u+w))
  for ep in sg:
   pair=tuple(v*w for v,w in zip(e,ep)); assert f(ep,f(e,z))==f(pair,z) and g(ep,g(e,z))==g(pair,z)
 for act,coord in [(f,1),(g,0)]:
  pts={(coord,h,k,0) for h,k in product(range(2),repeat=2)}
  assert {tuple(c%2 for c in act(e,z)) for z in pts}==pts
 assert all(c%2==0 for c in f(e,(0,0,0,0)))
print("PASS 16 signs, group composition, normalized reconstruction, dyadic closed unions.")
