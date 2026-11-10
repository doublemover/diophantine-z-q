#!/usr/bin/env python3
import itertools,json,random
import sympy as s
c=dict(symbolic_taylor=0,actual_gradients=0,explicit_affine_fibers=0,pivot_inverse=0,actual_integer_lift_equivalences=0,primitive_digit_counts=0,prime_power_counts=0)
k,m=s.symbols('k m');x=s.symbols('a b c d w');h=s.symbols('A B C D W')
def Q(k,x):a,b,c,d,w=x;return a*a+b*b-c*c-d*d-k*w*w
def grad(k,x):a,b,c,d,w=x;return (2*a,2*b,-2*c,-2*d,-2*k*w)
def der(k,x,h):return sum(a*b for a,b in zip(grad(k,x),h))
assert s.expand(Q(k,tuple(a+m*b for a,b in zip(x,h)))-Q(k,x)-m*der(k,x,h)-m*m*Q(k,h))==0;c['symbolic_taylor']=1
rng=random.Random(318326)
for p in [3,5,7]:
 allh=list(itertools.product(range(p),repeat=5))
 for k in [1,2,318,326]:
  if k%p==0:continue
  Rs=[v for v in allh if Q(k,v)%p==0 and any(v)]
  for v in Rs:
   assert any(a%p for a in grad(k,v));c['actual_gradients']+=1
  samples=[Rs[j] for j in sorted(set([0,len(Rs)//3,len(Rs)//2,len(Rs)-1]))]
  samples += [(1+p**e,0,1,0,0) for e in [2,3]]
  for idx,v in enumerate(samples):
   modulus=p if idx<4 else p**([2,3][idx-4]);assert Q(k,v)%modulus==0
   off=Q(k,v)//modulus;g=[a%p for a in grad(k,v)];i=next(i for i,a in enumerate(g) if a)
   fibers=[]
   for u in allh:
    a=Q(k,tuple(v[j]+modulus*u[j] for j in range(5)))%(p*modulus)==0
    b=(off+sum(g[j]*u[j] for j in range(5)))%p==0
    assert a==b;c['actual_integer_lift_equivalences']+=1
    if a:fibers.append(u)
   assert len(fibers)==p**4;c['primitive_digit_counts']+=1
   if idx>=4:c['prime_power_counts']+=1
   encoded={tuple(u[j] for j in range(5) if j!=i) for u in fibers};assert len(encoded)==p**4
   fiberSet=set(fibers)
   for free in encoded:
    u=[];it=iter(free)
    for j in range(5):u.append(0 if j==i else next(it))
    u[i]=(-off-sum(g[j]*u[j] for j in range(5) if j!=i))*pow(g[i],-1,p)%p
    assert tuple(u) in fiberSet;c['pivot_inverse']+=1
   c['explicit_affine_fibers']+=1
print(json.dumps({'status':'PASS','checks':c,'scope':'Exact original quadratic Taylor identity, actual primitive gradient, explicit four-free-coordinate lift equivalence, and literal p^e to p^(e+1) digit counts. Ambient residue reconstruction and full local density/circle method are not yet asserted.'},sort_keys=True))
