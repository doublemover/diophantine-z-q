#!/usr/bin/env python3
"""Exact squareclass of the relative tangent double cover of the actual split."""
from itertools import product,permutations
from math import prod,isqrt
from fractions import Fraction as F
from pathlib import Path
import json,sys
H=Path(__file__).resolve().parent
OWNER=H.parent/'actual-one-I-split-isogeny-selmer-r1'
sys.path.insert(0,str(OWNER))
import check_isogenous_exact_selmer as S
p=114649;q=119851;b=4921145;B=41579528353
X=(1476564103,1510668638,90243)
Y=(3741536523,2063719442,743003829)
SS=tuple(sorted({*S.support,37,271,82555981}))

def prime(z):return z>1 and all(z%i for i in range(2,isqrt(z)+1))
def val(x,l):
    assert x
    q0=F(x);a,b=q0.numerator,q0.denominator;v=0
    while a%l==0:a//=l;v+=1
    while b%l==0:b//=l;v-=1
    return v,F(a,b)
def ton(n,p):
    assert p>2
    n%=p
    if not n:return 0
    if pow(n,(p-1)//2,p)!=1:return None
    if p%4==3:return pow(n,(p+1)//4,p)
    t=p-1;s=0
    while t%2==0:t//=2;s+=1
    w=next(a for a in range(2,p) if pow(a,(p-1)//2,p)==p-1)
    x=pow(n,(t+1)//2,p);b=pow(n,t,p);g=pow(w,t,p)
    while b!=1:
        m=next(k for k in range(1,s) if pow(b,2**k,p)==1)
        h=pow(g,2**(s-m-1),p)
        x=x*h%p;b=b*h*h%p;g=h*h%p;s=m
    assert x*x%p==n
    return x

def root(a,l,N):
    assert a and S.cl(a,l)==0
    v,w=val(a,l);assert v>=0 and v%2==0
    k=N-v//2+int(l==2)
    assert k>=3
    m=l**k
    U=w.numerator*pow(w.denominator,-1,m)%m
    if l==2:
        T=[1]
        for j in range(1,k):
            T=[x+h*2**j for x in T for h in (0,1)
               if ((x+h*2**j)**2-U)%(2**(j+1))==0]
            assert T
        x=min(T)
    else:
        x=ton(U,l);assert x is not None
        M=l
        for _ in range(1,k):
            t=((U-x*x)//M)*pow(2*x,-1,l)%l
            x+=M*t
            M*=l
    assert (x*x-U)%m==0
    return (l**(v//2)*x)%(l**N)
def choices(l):
    yield (0,1);yield (1,0)
    if B%l==0 or b%l==0:
        k=1 if B%l==0 else 9
        x=ton(k*p*pow(q,-1,l),l);assert x is not None
        for j in range(20):
            yield (x+j*l,1)
    for x,y in product(range(35),repeat=2):
        if x%l or y%l:yield (x,y)

def local_witness(l):
    M=l**12
    for a,c in choices(l):
        u0=F(p*c*c-q*a*a,B)
        v0=F(9*p*c*c-q*a*a,b)
        if not u0 or not v0 or S.cl(u0,l) or S.cl(v0,l):continue
        u=root(u0,l,12);v=root(v0,l,12)
        A=(q*X[0]*a-p*X[1]*c+B*X[2]*u)%M
        C=(q*Y[0]*a-9*p*Y[1]*c+b*Y[2]*v)%M
        if not A or not C:continue
        if max(val(A,l)[0],val(C,l)[0])>(9 if l==2 else 11):continue
        return dict(a=a,c=c,u_mod_l12=u,v_mod_l12=v,L1_mod_l12=A,L2_mod_l12=C,
                    tangent_ratio_class=S.cl(A,l)^S.cl(C,l),p=l)
    assert False,l

def para(seed,Q):
    a,b,u=seed
    return ((-q*a,2*Q*b,-Q*a),(q*b,-2*q*a,Q*b),(q*u,0,-Q*u))
def poly2(R):
    return tuple(sum(a*b for i,a in enumerate(R) for j,b in enumerate(R) if i+j==s)
                 for s in range(5))
def det(A):
    n=len(A)
    return sum((-1)**sum(t[i]>t[j] for i in range(n) for j in range(i+1,n))*
               prod(A[i][t[i]] for i in range(n)) for t in permutations(range(n)))
def res(A,C):
    a,b,c=A;d,e,f=C
    return det(((a,b,c,0),(0,a,b,c),(d,e,f,0),(0,d,e,f)))

def main():
    assert all(prime(l) for l in SS)
    assert X[2]==3**2*37*271 and Y[2]==3**2*82555981
    assert q*X[0]**2-p*X[1]**2==-B*X[2]**2
    assert q*Y[0]**2-9*p*Y[1]**2==-b*Y[2]**2
    R,T=para(X,p),para(Y,9*p)
    for A,Q,f,s in ((R,p,B,X),(T,9*p,b,Y)):
        assert all(q*a-Q*b+f*c==0 for a,b,c in zip(*(poly2(z) for z in A)))
        assert res(*A[:2])==4*q*Q*f*f*s[2]**4
    raw=(OWNER/'EXACT-ISOGENOUS-SEL2.json').read_bytes()
    w={v['p']:v for v in json.loads(raw)['local']}
    I={}
    for l in SS:
        if l not in w:
            I[l]={0,2} # good prime unramified x-class
            continue
        h=3 if l==2 else 2
        V=[a[2]&((1<<h)-1) for a in w[l]['witnesses']]
        I[l]={0}
        for k in V:I[l]|={k^x for x in I[l]}
    wit=[local_witness(l) for l in SS]
    for z in wit:
        l=z['p'];bcl=z['tangent_ratio_class']
        z['affine_local_classes']=sorted(bcl^i for i in I[l])
    D=[1]
    stages=[]
    for l in SS:D+=[l*x for x in D]
    assert len(D)==2**len(SS)
    # The real x-map is positive and our two tangent values are negative on
    # (a,c)=(0,1), u<0, v<0. Thus ξ must be positive.
    for z in wit:
        l=z['p']
        D=[a for a in D if S.cl(a,l) in z['affine_local_classes']]
        stages.append([l,len(D)])
    assert D
    xi=min(D)
    eqs=[list(R[i])+[-xi*x for x in T[i]] for i in range(2)]
    print(json.dumps(dict(negative_seeds=[X,Y],projective_R=R,projective_T=T,
                resultants=[res(*R[:2]),res(*T[:2])],
                possible_positive_squareclasses=sorted(D),primes=SS,
                stage_counts=stages,chosen_xi=xi,actual_degree2_lift_quadrics=eqs,
                coefficient_order=["m²","mn","n²","r²","rs","s²"],exact_local_witnesses=wit),
              indent=2,sort_keys=True))
if __name__=='__main__':main()
