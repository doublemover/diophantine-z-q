"""Check literal 0-intermediate-prime r155 support template for both controls."""
from math import prod,isqrt
import json
for q0 in (19,127):
    for ps in ([q0,17],[q0,17,409]):
        assert all(all(p%k for k in range(2,isqrt(p)+1)) for p in ps)
        n=len(ps); assert len(set(ps))==n
        bit=lambda a,p: int(pow(a%p,(p-1)//2,p)==p-1)
        L=[[0 if i==j else bit(v,p) for j,v in enumerate(ps)] for i,p in enumerate(ps)]
        for i,row in enumerate(L):row[i]=sum(row)%2
        beta=[0,1]+([0] if n==3 else []);sel=[1,1]+([0] if n==3 else [])
        lam=[bit(3,p) for p in ps];par=[(p//2)%2 for p in ps]
        C=[[(L[i][j]+lam[i]*sel[j])%2 for j in range(1,n)] for i in range(1,n)]
        assert C==[[int(i==j) for j in range(n-1)] for i in range(n-1)]
        assert all(sum(a*b for a,b in zip(row,beta))%2==0 for row in L)
        assert prod(ps)%12==11 and (sum(sel)%2,sum(i*j for i,j in zip(sel,beta))%2)==(0,1)
        if n==3: assert not bit(409,17) and not bit(17,409)
        print(json.dumps(dict(support=ps,product=prod(ps),mod24=prod(ps)%24,
            laplacian=L,lambda_bits=lam,parity=par,deleted_sharp_core=C)))
from fractions import Fraction as F
P=[]
for d,uvw,h in [(2159,(59011852707419,239008613057229,62037827327035),980509883288),
              (883031,(163529,448239,267415),536)]:
    u,v,w=[F(i,h) for i in uvw];x=17*u*u;y=17*u*v*w
    assert x-d==v*v and x+3*d==17*w*w and y*y==x*(x-d)*(x+3*d) and y!=0
    P.append((u,y))
c=F(204,1073); b=c*c;B=17*b;V=B**2*(1-b/17);D=B*F(53,1073)
(u,y),(U,Y)=P; E=2159*(c/u)**2;s=U*D/u;y1=y*(c/u)**3;y2=Y*(c*D/u)**3
def f(e,x):return x*(x-e)*(x+3*e)
assert B==17*c*c and V==409*D*D
assert E*s*y1*y2 and y1*y1==f(E,B) and y2*y2==f(E*V,B*s*s)
print(json.dumps({'exact_point_pair':dict(zip(('b','E','s','y1','y2'),map(str,(b,E,s,y1,y2))))}))
