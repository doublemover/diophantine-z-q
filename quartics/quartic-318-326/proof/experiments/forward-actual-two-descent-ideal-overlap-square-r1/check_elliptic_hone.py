from itertools import product
import json
counts=dict(quadratic_fields=0,curves=0,geometric_points=0,actual_cocycles=0,actual_coboundaries=0,torsion_kernel_lifts=0,halved_cocycle_reductions=0,restriction_action_squares=0)
for p in [5,7,11,13]:
 d=next(a for a in range(2,p) if pow(a,(p-1)//2,p)==p-1)
 zero=(0,0);one=(1,0)
 def c(a):return(a%p,0)
 def add(a,b):return((a[0]+b[0])%p,(a[1]+b[1])%p)
 def neg(a):return(-a[0]%p,-a[1]%p)
 def sub(a,b):return add(a,neg(b))
 def mul(a,b):return((a[0]*b[0]+d*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
 def inv(a):
  k=pow((a[0]*a[0]-d*a[1]*a[1])%p,-1,p);return(a[0]*k%p,-a[1]*k%p)
 def div(a,b):return mul(a,inv(b))
 def sq(a):return mul(a,a)
 def plus(P,R,n):
  if P is None:return R
  if R is None:return P
  x,y=P;u,v=R
  if x==u and y==neg(v):return None
  if x==u:m=div(add(add(mul(c(3),sq(x)),mul(mul(c(4),n),x)),neg(mul(c(3),sq(n)))),mul(c(2),y))
  else:m=div(sub(v,y),sub(u,x))
  X=sub(sub(sub(sq(m),mul(c(2),n)),x),u)
  return(X,sub(mul(m,sub(x,X)),y))
 def minus(P):return None if P is None else(P[0],neg(P[1]))
 def frob(P):return None if P is None else((P[0][0],-P[0][1]%p),(P[1][0],-P[1][1]%p))
 elems=list(product(range(p),repeat=2));root={}
 for y in elems:root.setdefault(sq(y),[]).append(y)
 for nv in [1,2,3]:
  n=c(nv);points=[None]
  for x in elems:
   rhs=mul(mul(x,sub(x,n)),add(x,mul(c(3),n)))
   points +=[(x,y) for y in root.get(rhs,[])]
  boundary=lambda Q:plus(frob(Q),minus(Q),n)
  cycles={T for T in points if plus(frob(T),T,n) is None}
  bounds={boundary(Q) for Q in points}
  assert cycles==bounds # exact finite-field Hilbert90/Lang check, not an assumed theorem in Lean
  tors={T for T in points if plus(T,T,n) is None};assert len(tors)==4
  for T in tors:
   Q=next(Q for Q in points if boundary(Q)==T)
   P=plus(Q,Q,n);assert frob(P)==P
   assert boundary(Q)==T
   counts['torsion_kernel_lifts']+=1
  for R in points[:30]:
   Q=plus(R,R,n);bQ=boundary(Q)
   for z in cycles:
    if plus(z,z,n)!=bQ:continue
    w=plus(z,minus(boundary(R)),n)
    assert w in tors
    assert plus(w,boundary(R),n)==z
    counts['halved_cocycle_reductions']+=1
  for P in points:
   for Q in points[:8]:
    assert frob(plus(P,Q,n))==plus(frob(P),frob(Q),n)
    assert boundary(plus(P,Q,n))==plus(boundary(P),boundary(Q),n)
    counts['restriction_action_squares']+=1
  counts['curves']+=1;counts['geometric_points']+=len(points)
  counts['actual_cocycles']+=len(cycles);counts['actual_coboundaries']+=len(bounds)
 counts['quadratic_fields']+=1
print(json.dumps({'status':'PASS','scope':'Exact actual finite quadratic elliptic-group Galois/cocycle/kernel/halving regressions; not Lean or rational Sha verification','counts':counts},sort_keys=True,indent=2))
