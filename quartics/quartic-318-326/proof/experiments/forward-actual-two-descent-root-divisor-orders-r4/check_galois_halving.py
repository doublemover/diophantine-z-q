from itertools import product
import json
counts=dict(fields=0,twists=0,extension_points=0,rational_points=0,half_points=0,cocycle_checks=0,half_independence=0,additivity=0,kernel_checks=0,fixed_coordinates=0)
for p in [5,7,11,13]:
 d=next(d for d in range(2,p) if pow(d,(p-1)//2,p)==p-1)
 z=(0,0);one=(1,0)
 def add(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
 def neg(a):return(-a[0]%p,-a[1]%p)
 def sub(a,b):return add(a,neg(b))
 def mul(a,b):return ((a[0]*b[0]+d*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
 def inv(a):
  v=pow((a[0]*a[0]-d*a[1]*a[1])%p,-1,p)
  return(a[0]*v%p,-a[1]*v%p)
 def div(a,b):return mul(a,inv(b))
 def sq(a):return mul(a,a)
 def c(n):return(n%p,0)
 def frob(a):return(a[0],-a[1]%p)
 E=list(product(range(p),repeat=2));roots={}
 for y in E:roots.setdefault(sq(y),[]).append(y)
 counts['fields']+=1
 for x in E:
  assert (frob(x)==x)==(x[1]==0);counts['fixed_coordinates']+=1
 for n in [1,2,3]:
  if n%p==0:continue
  def curve(x):return mul(mul(x,sub(x,c(n))),add(x,c(3*n)))
  pts=[None]+[(x,y) for x in E for y in roots.get(curve(x),[])]
  R=[P for P in pts if P is None or P[0][1]==P[1][1]==0]
  def pn(P):return None if P is None else(P[0],neg(P[1]))
  def plus(P,Q):
   if P is None:return Q
   if Q is None:return P
   x,y=P;u,v=Q
   if x==u and y==neg(v):return None
   if x==u:m=div(add(add(mul(c(3),sq(x)),mul(c(4*n),x)),c(-3*n*n)),mul(c(2),y))
   else:m=div(sub(v,y),sub(u,x))
   X=sub(sub(sub(sq(m),c(2*n)),x),u)
   Y=sub(mul(m,sub(x,X)),y)
   return(X,Y)
  def F(P):return None if P is None else(frob(P[0]),frob(P[1]))
  halves={P:[] for P in R}
  for Q in pts:
   P=plus(Q,Q)
   if P in halves:halves[P].append(Q)
  tors={P for P in R if plus(P,P) is None};assert len(tors)==4
  delta={}
  for P in R:
   assert len(halves[P])==4
   values=[]
   for Q in halves[P]:
    v=plus(F(Q),pn(Q));assert v in tors
    assert plus(v,F(v)) is None
    values.append(v);counts['half_points']+=1;counts['cocycle_checks']+=2
   assert len(set(values))==1;counts['half_independence']+=16
   delta[P]=values[0]
   assert (values[0] is None)==any(plus(Q,Q)==P for Q in R);counts['kernel_checks']+=1
  for P,Q in product(R,repeat=2):
   assert delta[plus(P,Q)]==plus(delta[P],delta[Q]);counts['additivity']+=1
  counts['extension_points']+=len(pts);counts['rational_points']+=len(R);counts['twists']+=1
print(json.dumps({'status':'PASS','scope':'Exact finite quadratic-field analogue; not a Lean build or proof of Qbar topology/cohomology','counts':counts},sort_keys=True,indent=2))
