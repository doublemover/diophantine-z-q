from fractions import Fraction as Q
from itertools import product
import json
counts=dict(characteristic_zero_fields=0,nonrational_parameters=0,root_halves=0,root_translations=0,torsion_products=0,first_exceptional_halves=0,last_exceptional_halves=0)
for d in [2,3,5,7]:
 z=(Q(0),Q(0));one=(Q(1),Q(0))
 def c(a):return(Q(a),Q(0))
 def add(a,b):return(a[0]+b[0],a[1]+b[1])
 def neg(a):return(-a[0],-a[1])
 def sub(a,b):return add(a,neg(b))
 def mul(a,b):return(a[0]*b[0]+d*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
 def inv(a):
  D=a[0]*a[0]-d*a[1]*a[1];assert D
  return(a[0]/D,-a[1]/D)
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
  Y=sub(mul(m,sub(x,X)),y)
  return X,Y
 def curve(P,n):
  if P is None:return True
  x,y=P
  return sq(y)==mul(mul(x,sub(x,n)),add(x,mul(c(3),n)))
 def half(x,a,b,cc):return(add(add(add(x,mul(a,b)),mul(a,cc)),mul(b,cc)),neg(mul(mul(add(a,b),add(a,cc)),add(b,cc))))
 for i,j in product(range(-2,3),repeat=2):
  if j==0:continue
  t=(Q(i),Q(j));den=add(sq(t),c(3));a=one;b=div(mul(c(4),t),den);cc=div(mul(c(2),sub(c(3),sq(t))),den)
  n=sub(one,sq(b))
  if n==z:continue
  x=one;y=neg(mul(mul(a,b),cc));P=x,y;R=half(x,a,b,cc)
  assert curve(P,n) and curve(R,n) and plus(R,R,n)==P
  counts['nonrational_parameters']+=n[1]!=0;counts['root_halves']+=1
  for S,T in [(half(x,a,neg(b),neg(cc)),(z,z)),(half(x,neg(a),b,neg(cc)),(n,z)),(half(x,neg(a),neg(b),cc),(neg(mul(c(3),n)),z))]:
   assert plus(R,T,n)==S;counts['root_translations']+=1
  tors=[None,(z,z),(n,z),(neg(mul(c(3),n)),z)];signs=[(1,1),(-1,-1),(-1,1),(1,-1)]
  for u,v in product(range(4),repeat=2):
   out=plus(tors[u],tors[v],n);k=tors.index(out)
   assert signs[k]==tuple(a*b for a,b in zip(signs[u],signs[v]));counts['torsion_products']+=1
  aa=t;nn=sq(aa);R=half(nn,aa,z,mul(c(2),aa));assert plus(R,R,nn)==(nn,z);counts['first_exceptional_halves']+=1
  if d==3:
   u=(Q(0),Q(1));v=t;nn=neg(sq(v));xx=neg(mul(c(3),nn));R=half(xx,mul(u,v),mul(c(2),v),z)
   assert plus(R,R,nn)==(xx,z);counts['last_exceptional_halves']+=1
 counts['characteristic_zero_fields']+=1
print(json.dumps({'status':'PASS','scope':'Exact nonordered characteristic-zero quadratic base fields; actual original group/halves/translations, not Lean or infinite Galois verification','counts':counts},sort_keys=True,indent=2))
