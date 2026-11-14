from itertools import product
import json
counts=dict(fields=0,twists=0,extension_points=0,rational_points=0,half_points=0,cocycle_checks=0,half_independence=0,additivity=0,kernel_checks=0,fixed_coordinates=0,root_triples=0,root_flips=0,torsion_table=0,nonexceptional_comparisons=0,full_comparisons=0,first_explicit_halves=0,last_explicit_halves=0)
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
  signs={None:((1,0),(1,0)),((0,0),(0,0)):((p-1,0),(p-1,0)),((n%p,0),(0,0)):((p-1,0),(1,0)),((-3*n%p,0),(0,0)):((1,0),(p-1,0))}
  for T,U in product(tors,repeat=2):
   assert signs[plus(T,U)]==tuple(mul(v,w) for v,w in zip(signs[T],signs[U]));counts['torsion_table']+=1
  for P in R:
   if P is None:continue
   x,y=P
   for a,b,cc in product(roots.get(x,[]),roots.get(sub(x,c(n)),[]),roots.get(add(x,c(3*n)),[])):
    if mul(mul(a,b),cc)!=neg(y):continue
    def half(a,b,cc):return(add(add(add(x,mul(a,b)),mul(a,cc)),mul(b,cc)),neg(mul(mul(add(a,b),add(a,cc)),add(b,cc))))
    Q=half(a,b,cc);assert plus(Q,Q)==P;counts['root_triples']+=1
    for flipped,T in [(half(a,neg(b),neg(cc)),((0,0),(0,0))),(half(neg(a),b,neg(cc)),((n%p,0),(0,0))),(half(neg(a),neg(b),cc),((-3*n%p,0),(0,0)))]:
     assert plus(Q,T)==flipped;counts['root_flips']+=1
    if a!=z and b!=z and cc!=z:
     delta=plus(F(Q),pn(Q))
     assert signs[delta]==(div(frob(cc),cc),div(frob(b),b));counts['nonexceptional_comparisons']+=1
  def scalar_char(a):
   r=roots[a][0];return div(frob(r),r)
  for P in R:
   if P is None:expected=((1,0),(1,0))
   else:
    x,y=P;A=add(x,c(3*n));BB=sub(x,c(n))
    if A==z:A=c(12*n*n)
    if BB==z:BB=c(4*n*n)
    expected=(scalar_char(A),scalar_char(BB))
   for Q in halves[P]:
    assert signs[plus(F(Q),pn(Q))]==expected;counts['full_comparisons']+=1
  for a in roots[c(n)]:
   x=c(n);Q=half(a,z,mul(c(2),a))
   assert plus(Q,Q)==(c(n),z)
   assert signs[plus(F(Q),pn(Q))]==(scalar_char(c(n)),(1,0));counts['first_explicit_halves']+=1
  for u,v in product(roots[c(3)],roots[c(-n)]):
   x=c(-3*n);Q=half(mul(u,v),mul(c(2),v),z)
   assert plus(Q,Q)==(c(-3*n),z)
   assert signs[plus(F(Q),pn(Q))]==(scalar_char(c(3)),scalar_char(c(-n)));counts['last_explicit_halves']+=1
  counts['extension_points']+=len(pts);counts['rational_points']+=len(R);counts['twists']+=1
print(json.dumps({'status':'PASS','scope':'Exact full original cubic Kummer/Galois comparison, including all adjusted torsion coordinates and explicit exceptional halves, over finite quadratic fields; not a Lean build','counts':counts},sort_keys=True,indent=2))
