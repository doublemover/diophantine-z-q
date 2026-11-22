from itertools import combinations_with_replacement
from fractions import Fraction as F
import math
# Laurent q-expansion on X_0(48), pullback of rank-six Riemann--Roch basis.
L=250
def mul(a,b,T=None):
    r={}
    for i,v in a.items():
        for j,w in b.items():
            if T is None or i+j<=T:r[i+j]=r.get(i+j,0)+v*w
    return {i:v for i,v in r.items() if v}
def scale(a,k,shift=0):return {i+shift:v*k for i,v in a.items() if k}
def add(a,b):
    c=a.copy()
    for i,v in b.items():c[i]=c.get(i,0)+v
    return {i:v for i,v in c.items() if v}
ds={4:1,16:2,24:3,8:-3,12:-1,48:-2}
A={0:1}
for a,e in ds.items():
    for i in range(a,L+1,a):
        b={j*i:(-1)**j*math.comb(e,j) if e>0 else math.comb(-e+j-1,j)
            for j in range((min(e,L//i) if e>0 else L//i)+1)}
        A=mul(A,b,L)
assert A[0]==1
Am={0:1}
for n in range(1,L+1):Am[n]=-sum(A.get(i,0)*Am[n-i] for i in range(1,n+1))
Am={i:v for i,v in Am.items() if v}
XP={0:{0:1},1:scale(A,1,-1),-1:scale(Am,1,1)}
def pX(k):
    if k not in XP:
        XP[k]=mul(XP[1 if k>0 else -1],pX(k-1 if k>0 else k+1),L+8)
    return XP[k]
# Y=X^4 sqrt(1+14/X^4+1/X^8). Integral coefficients verified.
ser={}
for n in range(1+L//4):
    cc=(14 if n==1 else 1 if n in (0,2) else 0)
    ser[n]=1 if n==0 else F(cc-sum(ser[j]*ser[n-j] for j in range(1,n)),2)
assert all(k.denominator==1 for k in map(F,ser.values()))
B=[{0:1}]
for k in range(5):
    c={}
    for j,s in ser.items():
        e=4+k-4*j
        if e>L:continue
        s*=2 if e>0 else 1
        c=add(c,scale(pX(e),s))
    B.append({i:v for i,v in c.items() if i<=210})
assert [(min(b),b[min(b)]) for b in B]==[(0,1),(-4,2),(-5,2),(-6,2),(-7,2),(-8,2)]
T=140;D=[]
IJ=list(combinations_with_replacement(range(6),2))
for i,j in IJ:
    G=mul(B[i],{7*k:v for k,v in B[j].items()},T)
    if i!=j:
        G=add(G,mul(B[j],{7*k:v for k,v in B[i].items()},T))
    D.append(G)

C7={(0,0):2,(0,5):2,(1,1):-2,(2,2):-1,(3,3):2,(4,4):-1}
assert all(sum(C7.get(ij,0)*d.get(i,0) for ij,d in zip(IJ,D))==0 for i in range(-64,135))
