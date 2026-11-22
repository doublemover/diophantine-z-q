#!/usr/bin/env python3
from math import isqrt
from pathlib import Path
import json
S=json.loads(Path(__file__).with_name("PINNED-SCALAR-FIBER.json").read_text())
h,J,R,N=[S[k] for k in ("h","J","R_input","N")]
assert h==473592745039516333133760 and N==65536
beta=114444*R//(17*12**2)
assert beta==204618888056724185
t=18
A=1+3*beta*t*t
n=beta*(1-beta*t*t)*(1-9*beta*t*t)
X,Y=beta*A*A,8*beta*beta*t*A*(1-3*beta*t*t)
assert n==8094120968054829661910126903116889587959583856144085429185
assert X-n==(4*beta*t)**2 and X+3*n==beta*(2*(1-3*beta*t*t))**2
assert Y*Y==X*(X-n)*(X+3*n)
def sign(x,p):
    return {0:0,1:1,p-1:-1}[pow(x%p,(p-1)//2,p)]
places=[]
for p,delta_stripped in [(6551,684),(16782959,13715188)]:
    # delta data come from the two identified upstream exact p² controls.
    assert all(p%k for k in range(2,isqrt(p)+1)) and n%p and beta%p
    assert sign(beta,p)==1 and 0<delta_stripped<p
    roots=[0,n,-3*n]
    halves=[[sign(a-b,p) for b in roots if a!=b] for a in roots]
    places.append(dict(p=p,n_mod=n%p,delta_stripped_mod=delta_stripped,
                       v_delta_from_bound_upstream=1,
                       root_difference_signs=halves,
                       only_halvable_nonzero_root=next(i for i,f in enumerate(halves) if f==[1,1])))
assert [v["only_halvable_nonzero_root"] for v in places]==[2,1]

# Distinguish this old scalar from the trace field at the archived other h.
p=61
ann=3700
assert sign(2,p)==-1
def add(a,b):return tuple((x+y)%p for x,y in zip(a,b))
def neg(a):return tuple(-x%p for x in a)
def sub(a,b):return add(a,neg(b))
def mul(a,b):return (a[0]*b[0]+2*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p
def sq(a):return mul(a,a)
def norm(a):return (a[0]**2-2*a[1]**2)%p
def inv(a):
    u=pow(norm(a),-1,p)
    return a[0]*u%p,-a[1]*u%p
def k(n):return n%p,0
d=sq((3,p-1))
P=((1,1),(0,2))
def on(P):
    if P is None:return True
    x,y=P
    return sq(y)==mul(x,sub(sq(x),d))
assert on(P)
def ec(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;z,w=Q
    if x==z:
        if add(y,w)==(0,0):return None
        assert y==w
        m=mul(sub(mul(k(3),sq(x)),d),inv(mul(k(2),y)))
    else:
        m=mul(sub(w,y),inv(sub(z,x)))
    xx=sub(sub(sq(m),x),z)
    T=xx,sub(mul(m,sub(x,xx)),y)
    assert on(T)
    return T
def times(n):
    Q=None
    for b in bin(n)[2:]:
        Q=ec(Q,Q)
        if b=="1":Q=ec(Q,P)
    return Q
assert times(ann) is None
i0=pow(6,15,ann)*pow(3,N,ann)*J%ann
h0=h%ann
assert times(i0) is None
x,y=times(h0)
U=mul(mul(k(2),y),inv(add(sq(x),d)))
H=norm(U); f=sq(U)[0]
assert H and R%p
Qp=0
r=pow(R,-1,p)
Np=(1+(H*r)**2+2*f*r)%p
W=Np*Np%p
D=1+114444*R
c=12*W*pow(D,-1,p)%p
delta=(1-beta*c*c)%p
assert (U,H,f,Np,W,c,delta)==((31,47),20,11,7,49,55,50)
assert sign(delta,p)==-1
print(json.dumps(dict(beta=beta,h=h,t=t,n=n,point=[X,Y],places=places,
  p61=dict(annihilator=ann,h_mod=h0,i_mod=i0,chart_h=U,H=H,Q=Qp,N=Np,W=W,c=c,delta=delta,
           delta_unit_sign=sign(delta,p)),
  scope="literal old scalar; two local trace restrictions and known first point; global trace and any companion point unresolved"),
  indent=2,sort_keys=True))
