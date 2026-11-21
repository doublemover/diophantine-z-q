#!/usr/bin/env python3
"""Literal [4]-lift of the selected alpha C_2 using three rational tangents.

No global quadratic form search or built-in rank routine. Exact local square
root intervals and affine linear solve for the two global twist classes.
"""
from fractions import Fraction as F
from math import gcd, isqrt, lcm, prod
from itertools import product
from pathlib import Path
from hashlib import sha256
import json

D=Path(__file__).resolve().parent
old=D.parent.parent/'joined-work-20261120/linked-detector-fixed-b-small-u-selmer-four-r2'
def load(name):
    return json.loads((old/name).read_text())
S2=load('EXACT-SEL2-258049.json')
P2=load('EXACT-CASSELS-258049.json')
u=258049;b=8912209*1185793321;t=F(1,2399)
lam=F(16*u**4+24*u*u+1,32*u*u)
e=[F(0),b*t,-b*lam]; d=[b,1,b]
assert S2['u']==P2['u']==u and S2['b']==P2['b']==b and S2['raw_mark']==d
assert S2['full_dim']==4 and P2['total']==1 and P2['d']==d and P2['d2']==[1,2,2]
assert [F(*x) for x in S2['roots']]==e and F(*S2['lambda_'])==lam
raw0=(0,1,2,
      [5111926338431968,-54023031325183434770223270653152,1798677552621956943360855958988962669002399],
      [6079505104844311364746767193278211085237450706529,576226963077860286378965833079167434787379,
       3141282794478630956203018136386712416])
ts=[raw0,*P2['tangents']]
L=[]
for i,j,k,co,P in ts:
    v=[F(d[j]),F(-d[k]),e[j]-e[k]]
    ratio=F(co[0],v[0]); assert all(F(c)==ratio*q for c,q in zip(co,v))
    assert gcd(*P)==1 and sum(c*u*u for c,u in zip(co,P))==0
    coeff=[0,0,0,co[2]*P[2]]
    coeff[j]=co[0]*P[0];coeff[k]=co[1]*P[1]
    L.append(coeff) # do not drop any scaling, even when it is a unit
    assert L[-1][i]==0

def vp(q,p):
    q=F(q);n,d=q.numerator,q.denominator;k=0
    assert n
    while n%p==0:n//=p;k+=1
    while d%p==0:d//=p;k-=1
    return k,F(n,d)
def unitmod(q,m):
    return q.numerator*pow(q.denominator,-1,m)%m
def loc(q,p):
    if p==-1:return int(q<0)
    k,v=vp(q,p)
    if p==2:return (k%2)*4+{1:0,3:1,5:2,7:3}[unitmod(v,8)]
    E=pow(unitmod(v,p),(p-1)//2,p);assert E in (1,p-1)
    return (k%2)*2+int(E==p-1)
def width(p): return 1 if p==-1 else 3 if p==2 else 2
def bits(q,r,p): return loc(q,p)|(loc(r,p)<<width(p))
def powq(p,k):return F(p**k) if k>=0 else F(1,p**(-k))
def sqrtp(q,p,N=30):
    k,v=vp(q,p)
    if k%2:return None
    m=p**N;a=unitmod(v,m)
    if p==2:
        if a%8!=1:return None
        r=1
        for j in range(3,N):
            if (r*r-a)%2**(j+1):r+=2**(j-1)
            assert (r*r-a)%2**(j+1)==0
        return powq(p,k//2)*r,k//2+N-1
    if pow(a%p,(p-1)//2,p)==p-1:return None
    from sympy.ntheory.residue_ntheory import sqrt_mod
    r=int(sqrt_mod(a%p,p))
    assert (r*r-a)%p==0
    P=p
    for _ in range(1,N):
        r+=P*((a-r*r)//P*pow(2*r,-1,p)%p)
        P*=p
    assert (r*r-a)%m==0
    return powq(p,k//2)*r,k//2+N

def local_alpha_odd_or_two(p,want=None):
    # Exact rational centers near the three roots. The full [4]-cover only needs
    # a witness on original alpha for each p, not tiny measured contact balls.
    for h in sorted(range(-15,19),key=abs):
      for E in e:
       for r in range(1,100):
        if r%p==0:continue
        x=E+r*powq(p,h)
        if x in e:continue
        vals=[(x-E)/q for E,q in zip(e,d)]
        roots=[sqrtp(q,p) for q in vals]
        if any(s is None for s in roots):continue
        for signs in ([(1,1,1)] if want is None else product([1,-1],repeat=3)):
            z=[a[0]*sgn for a,sgn in zip(roots,signs)]+[F(1)]
            P=[a[1] for a in roots]
            out=[]
            for row in L:
                a=sum(c*h for c,h in zip(row,z))
                bound=min(vp(c,p)[0]+k for c,k in zip(row,P) if c)
                if not a or bound<vp(a,p)[0]+(3 if p==2 else 1):break
                out.append(a)
            if len(out)==3 and (want is None or bits(out[1]*out[2],out[0]*out[2],p)==want):
              return [x,z,out,P]
    raise RuntimeError(('no local root witness within fixed diagnostic bound',p))

def local_alpha_real(want=None):
    # Exact dyadic bounds on the positive square roots.
    K=48
    x=F(b)
    z=[]
    for E,q in zip(e,d):
        a=(x-E)/q; assert a>0
        z.append(F(isqrt((a.numerator<<(2*K))//a.denominator),2**K))
    for signs in ([(1,1,1)] if want is None else product([1,-1],repeat=3)):
        zz=[a*sgn for a,sgn in zip(z,signs)]+[F(1)]
        out=[]
        for row in L:
            a=sum(c*q for c,q in zip(row,zz)); err=F(sum(abs(h) for h in row[:3]),2**K)
            if abs(a)<=err:break
            out.append(a)
        if len(out)==3 and (want is None or bits(out[1]*out[2],out[0]*out[2],-1)==want):
            return [x,zz,out,[K]*3]
    raise RuntimeError('no direct real representative in selected signs')

def dot(a,b):return (a&b).bit_count()%2
def basis(vs):
    B={}
    for u in vs:
        while u:
            j=u.bit_length()-1
            if j in B:u^=B[j]
            else:B[j]=u;break
    return B
def kernel(rows,dim):
    B=basis(rows);ans=[]
    for i in range(dim):
        if i in B:continue
        x=1<<i
        for j,u in sorted(B.items()):
            if dot(x,u):x^=1<<j
        assert not any(dot(x,u) for u in rows)
        ans.append(x)
    return ans

S2_support=list(map(int,S2['support']))
S=sorted(set(S2_support)|{5,7,13,17})
images={int(p):{int(k):v for k,v in im.items()} for p,im in S2['local_images'].items()}
for p in S:
    if p not in images:images[p]={0:None,1:None,4:None,5:None}
assert len(S2_support)==15 and len(S)==19
# i=0 and i=1 pushouts: g0=L1*L2/H²; g1=L0*L2/H².
# Their global squareclasses at every p must belong to an affine translate
# of the first-two-coordinate Kummer image on E(Q_p).
Rows=[];points={}
for p in S:
    x,z,ell,precision=local_alpha_real() if p==-1 else local_alpha_odd_or_two(p)
    off=bits(ell[1]*ell[2],ell[0]*ell[2],p)
    hp=dict(local_alpha_x=x,roots=z,tangent_values=ell,root_precisions=precision,
            affine_offset=off,locally_admissible_classes=sorted(off^v for v in images[p]))
    points[p]=hp
    d0=width(p);S0=[loc(g,p) for g in S]
    M0=S0+[h<<d0 for h in S0]
    for u0 in kernel(list(images[p]),2*d0):
        mask=sum(dot(c,u0)<<i for i,c in enumerate(M0))
        rhs=dot(u0,off)
        Rows.append((mask,rhs))

# Solve over F2 exactly, pivoting only variables, with zero free choice.
R={}
for s,t0 in Rows:
    while s:
        i=s.bit_length()-1
        if i in R:
            u0,v0=R[i];s^=u0;t0^=v0
        else:R[i]=s,t0;break
    else: assert not t0,'global affine Selmer-[4] lift failed'
Z=0
for i,(s,r) in sorted(R.items()):
    if dot(Z,s)!=r:Z^=1<<i
assert all(dot(Z,j)==v for j,v in Rows)
dim=2*len(S)-len(R)
assert dim==4
twists=[prod(g for j,g in enumerate(S) if (Z>>(i*len(S)+j))&1) for i in (0,1)]
assert all(bits(*twists,p) in points[p]['locally_admissible_classes'] for p in S)
for p in S:
    want=bits(*twists,p)
    x,z,ell,prec=local_alpha_real(want) if p==-1 else local_alpha_odd_or_two(p,want)
    points[p]['direct_lift_witness']=dict(x=x,roots=z,tangent_values=ell,root_precisions=prec)
def pack(x):
    if isinstance(x,F):return [x.numerator,x.denominator]
    raise TypeError(type(x))
print(json.dumps(dict(case_u=u,b=b,lambda_=lam,t=t,third_conic_seed=raw0,
      normalized_tangent_coefficients=L,finite_support=S,rank=len(R),affine_dimension=dim,
      affine_rows=Rows,one_global_twist_mask=Z,one_global_twist_xi=twists,
      exact_local_affine_memberships=points,
      joined_donors={n:sha256((old/n).read_bytes()).hexdigest()
          for n in ['EXACT-SEL2-258049.json','EXACT-CASSELS-258049.json']},
      scope='particular ELS [4]-cover by two normalized rational tangent pushouts; not T0 next pushout'),
      default=pack,sort_keys=True,indent=2))
