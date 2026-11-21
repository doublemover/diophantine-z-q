"""Exact a=617 source class, homogeneous graph factors, and fixed bad support."""
from fractions import Fraction as F
from math import gcd,isqrt,prod
import json

a=617; A0=2*a+1
A=(3723*A0*A0-2401)//2
B=(3723*A0*A0-1)//2
C=7446*A0*A0-1
D=119136*A0*A0+343
facts=((2839205137,), (11,601,429467), (359,31634611), (359,506153777))
assert tuple(prod(g) for g in facts)==(A,B,C,D)
ps=sorted({17,*[p for g in facts for p in g]}-{11,359})
assert all(p%8 in (1,3) and all(p%j for j in range(2,isqrt(p)+1)) for p in ps)
b=prod(ps)
R=4*A*B*C*D
br=187*R//4
assert br==b*(11*359)**2
K=1+2448*br
x,y=362538667625927811,184450110513594440
assert x*x+2*y*y==b and gcd(2*y,x)==1
z=F(2*y,x); lam=(z*z+2)/18
t0=F(1,3*x)
assert lam==b*t0*t0 and z*z-18*b*t0*t0==-2

def trim(xs):
    xs=list(xs)
    while len(xs)>1 and xs[-1]==0:xs.pop()
    return xs
def add(xs,ys):
    n=max(len(xs),len(ys));v=[F(0)]*n
    for i,j in enumerate(xs):v[i]+=j
    for i,j in enumerate(ys):v[i]+=j
    return trim(v)
def times(x,ys):return trim([x*y for y in ys])
def mul(xs,ys):
    v=[F(0)]*(len(xs)+len(ys)-1)
    for i,x in enumerate(xs):
        for j,y in enumerate(ys):v[i+j]+=x*y
    return trim(v)
def divmodp(xs,ys):
    xs=trim(xs);v=[F(0)]*(len(xs)-len(ys)+1)
    while xs!=[0] and len(xs)>=len(ys):
        i=len(xs)-len(ys);c=xs[-1]/ys[-1];v[i]+=c
        xs=add(xs,[F(0)]*i+times(-c,ys))
    return trim(v),xs
def val(xs,t):
    v=F(0)
    for p in reversed(xs):v=v*t+p
    return v
def res(xs,ys):
    m,n=len(xs)-1,len(ys)-1
    rows=[[F(0)]*i+list(reversed(xs))+[F(0)]*(n-1-i) for i in range(n)]
    rows += [[F(0)]*i+list(reversed(ys))+[F(0)]*(m-1-i) for i in range(m)]
    s=F(1)
    for i in range(m+n):
        r=next((j for j in range(i,m+n) if rows[j][i]),None)
        if r is None:return F(0)
        if r!=i:rows[r],rows[i]=rows[i],rows[r];s=-s
        p=rows[i][i];s*=p
        for j in range(i+1,m+n):
            q=rows[j][i]/p
            if q:
                rows[j]=[u-q*v for u,v in zip(rows[j],rows[i])]
    return s

W=[4-z*z,-2*(z*z+2)];U=[-(z+4),z+4]
w2=mul(W,W);u2=mul(U,U);wu=mul(W,U)
P=add(add(w2,times(z*z+2,u2)),times(-2*z,wu))
Q=add(w2,times(-(z*z+2),u2))
Y=add(times(-z,add(w2,times(z*z+2,u2))),times(2*(z*z+2),wu))
assert add(add(mul(Y,Y),times(-18*lam,mul(P,P))),times(2,mul(Q,Q)))==[0]
s1=[F(1),F(0),-lam];s9=[F(1),F(0),-9*lam]
L,remainder=divmodp(add(mul(Q,Q),times(-lam,mul(P,P))),s9)
assert remainder==[0] and len(L)==3 and res(P,Q)!=0
H=times(-F(1,2),mul(s1,L))
assert len(H)==5
assert val(Q,1)==val(P,1)!=0 and val(Y,1)==-z*val(Q,1)
y0=z**3*(z*z-16)/2
assert val(H,1)==y0*y0!=0
disc=res(H,[i*H[i] for i in range(1,5)])/H[-1]
rhs=F(1024,729)*z**16*(z-4)**2*(z+4)**8*(z*z+2)**6*(z*z-40*z-32)**2*(7*z**3+16*z*z+32*z+32)**2
assert disc==rhs!=0
p,q=z.numerator,z.denominator
parts=[p,p-4*q,p+4*q,p*p+2*q*q,p*p-40*p*q-32*q*q,7*p**3+16*p*p*q+32*p*q*q+32*q**3,q]
candidates=abs(6*prod(parts))
off=R*K*(K*K-144*br)
g=gcd(candidates,off)
while True:
    step=gcd(g,2*3*b)
    if step==1:break
    g//=step
assert g==1
small=[j for j in range(2,65) if all(j%d for d in range(2,isqrt(j)+1)) and candidates%j==0]
assert small==[2,3,5,13,17,47]
assert all(pow(b,(ell-1)//2,ell)==1 for ell in (5,13,47))
assert b%8==br%8==1 and br%3==2 and (br//17)%17==1
assert (1-br*(12*pow(K,-1,5))**2)%5==2

def v(n,p):
    assert n
    e=0
    while n%p==0:e+=1;n//=p
    return e
def vp(a,p):return v(a.numerator,p)-v(a.denominator,p)
ee,dd,cc,bb,aa=H
I=12*aa*ee-3*bb*dd+cc*cc
J=72*aa*cc*ee+9*bb*cc*dd-27*aa*dd*dd-27*bb*bb*ee-2*cc**3
assert (vp(I,13),vp(J,13),vp(4*I**3-J**2,13))==(0,0,2)
j=1728*4*I**3/(4*I**3-J**2)
jrows=[(p,vp(j,p)) for p in (2,3,5,13,17,47)]
assert jrows==[(2,2),(3,-6),(5,-4),(13,-2),(17,0),(47,-2)]
def dformal(m,p):
    W=(1+pow(m,4,p)*pow(R,-29,p))%p
    return (1-br*(12*W*pow(K,-1,p))**2)%p
modes=[(p,m,dformal(m,p)) for p,m in [(5,0),(13,0),(13,1),(47,2)]]
assert modes==[(5,0,2),(13,0,4),(13,1,5),(47,2,34)]
assert pow(5,6,13)==12 and pow(34,23,47)==1
def sl(xs):return [str(c) for c in xs]
print(json.dumps(dict(a=a,first_label=3723*A0**2,factors=facts,raw_beta=br,normalized_beta=b,
    source_R=R,source_K=K,integer_beta_norm=[x,y],z=str(z),lambda_value=str(lam),
    conic_P=sl(P),conic_Q=sl(Q),reduced_second_factor=sl(L),
    baseline_rational_point=["1",str(y0)],disc_nonzero=True,
    fixed_bad_candidate_factors=parts,fixed_coefficients_no_disallowed_prime=True,
    fixed_bad_small_primes=small,formal_modes=modes,j_valuations=jrows,
    I_J_discriminant_valuations_13=[0,0,2]),sort_keys=True,indent=2))
