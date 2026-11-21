from fractions import Fraction as F
from random import Random
from math import prod
R=Random(854_734)
roots=[F(0),-F(1,2),F(-1),F(1,2399),-F(32,407)]
def v(x,p):
    x=F(x)
    assert x
    a,b=x.numerator,x.denominator
    e=0
    while a%p==0: a//=p; e+=1
    while b%p==0: b//=p; e-=1
    return e
def sample(c,A,q,u):
    t=F(u,A*A*q); T=c*c*t
    K=[F(u)-th*A*A*q/(c*c) for th in roots]
    d=T-1; P=prod(T-i for i in roots)
    W=c**10*d*d/P
    W=[W,W**7*d**18,W**25*d**72]
    assert P==c**10/(A*A*q)**5*prod(K)
    return d,P,K,W
def coeff(w):
    return [
      (1,w[126],0),(0,w[125],0),(0,w[58],2*w[59]),(0,w[60],2*w[61]),
      (0,2*w[62],2*w[63]),(0,w[64],2*w[65]),(0,w[19]-1,-w[20]),
      (0,w[23]-1,-w[24]),(0,w[27]-1,-w[28]),(0,w[31]-1,-w[32]),
      (1,w[127],2*w[128]),(2,w[129],2*w[130]),(2,w[131],2*w[132]),
      (2,w[133],2*w[134]),
      (1,110885832*w[0]-7446*w[102]+110885832*w[118]+221771664*w[135]+13860729,-7446*w[103]-29784*w[136]),
      (2,-2*w[123]+w[137]+1,-4*w[124]+4*w[138])]
def fold(W,C,p):
    M=p**5
    def mod(x):
        x=F(x); return x.numerator*pow(x.denominator,-1,M)%M
    a,b=1,0
    for j,x,y in C:
        a,b=(a*a+2*b*b+mod(W[j]*x))%M,(2*a*b+mod(W[j]*y))%M
    assert a%p==1 and b%p==0 and (a*a-2*b*b)%p==1
    return v(F(a*a-2*b*b,2*a),p)
A0=4*2399*407*17**2*7*3
units=balanced=tests=0
qs=[1009,1033,1129,1201]
for _ in range(300):
    q=R.choice(qs); u=1+408*R.randint(1,1000)
    if u%q==0:continue
    A=A0*408**R.randint(0,2)
    c=R.choice([F(1),F(-2,3),F(17,7)])
    d,P,K,W=sample(c,A,q,u)
    assert all(k.denominator==1 for k in K)
    assert v(d,q)==-1 and v(P,q)==-5 and [v(x,q) for x in W]==[3,3,3]
    tr=F(R.choice([-5,-1,1,2,8])); z=tr/(A**5*q**3*d**3)
    pole=tr*tr*P/(c**10*d**6)
    assert pole==q*prod(K)*z*z and v(pole,q)==1 and v(z,q)==0
    C=coeff([R.randint(-500,500) for i in range(146)])
    assert fold(W,C,q)==0
    units+=1
    for p in [2,3,17]:
        av,cv,qv=v(A,p),v(c,p),v(q,p)
        if v(d,p)>=0 or any(v(k,p)!=0 for k in K):continue
        assert [v(x,p) for x in W]==[6*av+3*qv+e*cv for e in [4,64,244]]
        if min(v(x,p) for x in W)<=0:continue
        tv=fold(W,C,p)
        assert tv==-v(2,p)
        zv=tv-5*av-3*qv-3*v(d,p)
        assert zv==av-6*cv-v(2,p)
        assert qv+2*zv==2*av+qv-12*cv-2*v(2,p)
        balanced+=1
for j in range(1000):
    c=F(R.randint(1,50),R.randint(1,50)); A=R.randint(1,70)
    q=R.choice(qs); u=R.randint(-500,500)
    T=c*c*F(u,A*A*q)
    if T in roots or T==1:continue
    d,P,K,W=sample(c,A,q,u)
    tr=F(R.randint(-80,80),R.randint(1,80))
    assert tr*tr*P/(c**10*d**6)==q*prod(K)*(tr/(A**5*q**3*d**3))**2
    tests+=1
assert units>=295 and balanced>=300 and tests>=990
print(f'{units} order-only rational q folds, {balanced} fixed small-place unit/depth folds, {tests} signed exact rational identities')
