from itertools import product
from fractions import Fraction as F
from collections import defaultdict
import json
counts=defaultdict(int)
zero=(F(0),F(0));one=(F(1),F(0));roots=[one,(F(0),F(1)),(-F(1),F(0)),(F(0),-F(1))]
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(c,a):return(c*a[0],c*a[1])
def summ(xs):
 r=zero
 for x in xs:r=add(r,x)
 return r
def l1(a):return abs(a[0])+abs(a[1])
def shift(x,i,j):return tuple(v+j if k==i else v for k,v in enumerate(x))
def terms(g,steps,x,i=0):
 if i==len(steps):return [((),g(x))]
 N=steps[i];out=[((N+1,)+ns,c) for ns,c in terms(g,steps,shift(x,i,N),i+1)]
 gd=lambda z:g(z)-g(shift(z,i,1))
 for j in range(N):out += [((j+1,)+ns,c) for ns,c in terms(gd,steps,shift(x,i,j),i+1)]
 return out
def rect(g,steps,cs,lo,t):
 return summ(scale(g(js),roots[(t*sum(c*(l+j)**2 for c,l,j in zip(cs,lo,js)))%4]) for js in product(*(range(N+1) for N in steps)))
def pre(ns,cs,lo,t):
 r=one
 for n,c,l in zip(ns,cs,lo):r=mul(r,summ(roots[(t*c*(l+j)**2)%4] for j in range(n)))
 return r
for dim in range(1,6):
 for steps in [tuple([1]*dim),tuple(0 if i%2 else 2 for i in range(dim))]:
  cs=([1,1,-1,-1,-3])[:dim];lo=tuple(-i-1 for i in range(dim))
  # A truly non-product, periodic real weight. The all-order constant is
  # computed on its exact finite period, including repeated directions.
  g=lambda x:F((sum((i+1)*v for i,v in enumerate(x))+sum(x[i]*x[j] for i in range(dim) for j in range(i)))%3-1,2)
  ts=terms(g,steps,tuple([0]*dim))
  assert all(len(ns)==dim and all(1<=n<=N+1 for n,N in zip(ns,steps)) for ns,c in ts)
  for t in range(4):
   actual=rect(g,steps,cs,lo,t)
   expanded=summ(scale(c,pre(ns,cs,lo,t)) for ns,c in ts)
   assert actual==expanded;counts['exact_nonseparable_abel']+=1
  M=max(sum(l1(pre(ns,cs,lo,t)) for t in range(4)) for ns in product(*(range(N+2) for N in steps)))
  cost=sum(abs(c) for ns,c in ts)
  assert sum(l1(rect(g,steps,cs,lo,t)) for t in range(4))<=M*cost
  counts['finite_joint_prefix_integrals']+=1
  # Uniform bound |Delta^k g|<=2^k * ||g||inf <= (1/2)*2^k.
  # Hence rho=2,C=1/2,R=2*max(steps), independent of translations.
  assert cost<=F(1,2)*(1+2*max(steps))**dim
  counts['all_boundary_coefficient_budget']+=1
  counts['retained_boundary_terms']+=len(ts)
# Exact five signed-coordinate phase factorization on finite boxes.
for H in range(3):
 for k in [-3,-1,1,2]:
  for x in product(range(-H,H+1),repeat=5):
   q=x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2
   for t in range(4):
    z=one
    for c,v in zip([1,1,-1,-1,-k],x):z=mul(z,roots[(t*c*v*v)%4])
    assert roots[(t*q)%4]==z
   counts['original_five_phase_identity']+=1
# Negative controls: omitting terminal term, omitting mixed differences,
# factoring a nonseparable weight, and exchanging integral/max.
g=lambda x:F((x[0]+x[1]+x[0]*x[1])%3-1,2)
ts=terms(g,(1,1),(0,0));assert ts[0][1]!=0
assert any(ns==(1,1) and c!=0 for ns,c in ts)
assert g((0,0))*g((1,1))!=g((0,1))*g((1,0))
assert sum(max(row) for row in [[1,0],[0,1]])>max(sum(col) for col in zip(*[[1,0],[0,1]]))
counts['negative_controls']=4
print(json.dumps({'status':'PASS','checks':dict(counts),'scope':'Exact rational/Gaussian identities and coefficient budgets; finite integral triangle regression uses Gaussian l1 norm, not a numerical approximation of Euclidean norm or a proof of continuous integration.'},indent=2))
