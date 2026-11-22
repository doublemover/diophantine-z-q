"""Independent finite controls: actual [pi] vs one fixed p-Frobenius turn."""
from itertools import product
from math import isqrt
N=0
point_checks=0
for p in (5,13,17,29,37,41,53,61):
  n=(p-1)//2
  d=next(u for u in range(2,p) if pow(u,n,p)==p-1)
  def sum_(x,y): return (x[0]+y[0])%p,(x[1]+y[1])%p
  def neg(x): return -x[0]%p,-x[1]%p
  def sub(x,y): return sum_(x,neg(y))
  def mul(x,y):
    a,b=x; c,e=y
    return (a*c+d*b*e)%p,(a*e+b*c)%p
  def div(x,y):
    a,b=y
    inv=pow((a*a-d*b*b)%p,-1,p)
    return mul(x,(a*inv%p,-b*inv%p))
  def negP(P): return None if P is None else (P[0],neg(P[1]))
  def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    x,y=P; z,w=Q
    if x==z:
      if sum_(y,w)==(0,0): return None
      s=div(sub(mul((3,0),mul(x,x)),(1,0)),mul((2,0),y))
    else: s=div(sub(y,w),sub(x,z))
    X=sub(mul(s,s),sum_(x,z))
    return X,neg(sum_(y,mul(s,sub(X,x))))
  def smul(m,P):
    if m<0: return smul(-m,negP(P))
    Q=None
    while m:
      if m&1: Q=add(Q,P)
      m//=2
      if m: P=add(P,P)
    return Q
  allk=list(product(range(p),repeat=2))
  squares={}
  for y in allk: squares.setdefault(mul(y,y),[]).append(y)
  pts=[None]
  for x in allk: pts += [(x,y) for y in squares.get(sub(mul(mul(x,x),x),x),[])]
  def F(P):
    return None if P is None else tuple((x,-y%p) for x,y in P)
  q=[j for j in range(p) if (j*j+1)%p==0]
  B=isqrt(p)
  for j in q:
    S=[(a,b) for a,b in product(range(-B,B+1),repeat=2) if a*a+b*b==p and (a+b*j)%p==0]
    assert len(S)==4
    def J(P):
      return None if P is None else (neg(P[0]),mul((j,0),P[1]))
    def opts(P): return [P,negP(P),J(P),negP(J(P))]
    def g(a,b,P): return add(smul(a,P),smul(b,J(P)))
    for a,b in S:
      N+=1
      candidates=set(range(4))
      for P in pts:
        z=g(a,b,P)
        f=opts(F(P))
        candidates={k for k in candidates if z==f[k]}
        assert J(z)==g(-b,a,P)
        assert negP(z)==g(-a,-b,P)
        point_checks+=1
      # A single tag on all F_{p^2} stock points. This is a control only.
      assert len(candidates)==1
      t=candidates.pop()
      u,v=[(a,b),(-a,-b),(b,-a),(-b,a)][t]
      assert (u*u+v*v,(u+v*j)%p)==(p,0)
      for P in pts:
        assert g(u,v,P)==F(P)
      assert ((a+b)%4==1 and b%2==0)==(t==0)
print(f"signed norm-prime pairs / chosen roots: {N}")
print(f"all-stock-point comparisons (four unit versions): {point_checks}")
print("a single exact tag and its inverse coefficient rotation verified on every tested F_(p²) curve")
