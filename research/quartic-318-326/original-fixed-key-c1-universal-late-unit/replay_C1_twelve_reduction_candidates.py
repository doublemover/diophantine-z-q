"""Bounded F169 candidate check for the entire archived C1 fibre."""
from hashlib import sha256
import json
import sys

raw=open(sys.argv[1],"rb").read()
assert sha256(raw).hexdigest()=="8db46c10358d5db6b75a3bcbe735d2e1658c4d3c1557627c9ab1b83431354d6b"
prev=json.loads(raw)
assert prev["label_modulus"]==15*13**5
ns=prev["labels_n1_n2_n3"]
assert all((n-e)%195==0 for n,e in zip(ns,[1,-1,1]))
assert prev["valuation_and_stripped_digit"] == [[2,7],[4,2],[2,1],[4,7]]

p=13
zero=(0,0)
one=(1,0)
def add(x,y):
    return ((x[0]+y[0])%p,(x[1]+y[1])%p)
def neg(x):
    return ((-x[0])%p,(-x[1])%p)
def sub(x,y):
    return add(x,neg(y))
def mul(x,y):
    a,b=x;c,d=y
    return ((a*c+2*b*d)%p,(a*d+b*c)%p)
def sc(n,z):
    return mul((n,0),z)
def div(x,y):
    a,b=y;k=pow((a*a-2*b*b)%p,-1,p)
    return mul(x,(a*k%p,-b*k%p))
def pw(x,n):
    y=one
    for _ in range(n):y=mul(y,x)
    return y
D=pw((3,12),2)
def rhs(x):
    return sub(pw(x,3),mul(D,x))
def plus(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P; a,b=Q
    if x==a and y==neg(b):return None
    m=div(sub(sc(3,pw(x,2)),D),sc(2,y)) if P==Q else div(sub(b,y),sub(a,x))
    X=sub(sub(pw(m,2),x),a)
    Y=sub(mul(m,sub(x,X)),y)
    assert pw(Y,2)==rhs(X)
    return (X,Y)
def order(P):
    Q=None
    for n in range(1,31):
        Q=plus(Q,P)
        if Q is None:return n
    raise ValueError("outside expected small exact controls")
def R(P):
    return div(P[0],P[1])
def rho(P):
    return div(neg(add(pw(P[0],2),D)),P[1])
G=((1,1),(0,2)); T=plus(G,G)
assert order(G)==order(T)==15
r0=R(T);rho0=rho(T)
xs=[(a,b) for a in range(p) for b in range(p)]
def enc(P):
    assert P[1]!=zero and pw(P[1],2)==rhs(P[0])
    return [list(P[0]),list(P[1]),order(P)]
aroots=[a for a in range(1,p) if (a-1)*(a-2)*(4*a*a-9*a+4)%p==0]
assert aroots==[1,2,3,9]
a_rows={}
for a in aroots:
    r=div(r0,(a,0))
    z=div(one,pw(r,2))
    a_rows[str(a)]=[enc((x,div(x,r))) for x in xs if sub(sub(pw(x,2),mul(z,x)),D)==zero]
rho_rows=[]
for x in xs:
    y=div(neg(add(pw(x,2),D)),rho0)
    if pw(y,2)==rhs(x):
        rho_rows.append(enc((x,y)))
assert a_rows=={"1":[[[3,3],[2,4],30],[[12,3],[7,11],15]],"2":[],"3":[],"9":[]}
assert rho_rows==[[[0,5],[0,11],30],[[3,3],[11,9],30],
                  [[9,8],[1,11],30],[[12,3],[7,11],15]]
out={"field":"F_169, r^2=2, pair coordinates (1,r)","D":D,
     "target_Tstar":enc(T),"R_Tstar":r0,"rho_Tstar":rho0,
     "a_rows":a_rows,"rho_rows":rho_rows,"translated_origin_depths_pattern":[[17,4],[4,1]],
     "n1_subgroup_enumerated":False}
print(json.dumps(out,indent=2,sort_keys=True))
