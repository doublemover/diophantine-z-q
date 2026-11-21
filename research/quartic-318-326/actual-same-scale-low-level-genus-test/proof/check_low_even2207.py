#!/usr/bin/env python3
"""Exact 2-Selmer and Cassels witness for the fixed lower-level even companion."""
from fractions import Fraction as Q
from itertools import product
from math import gcd,isqrt,prod
from pathlib import Path
import json

W=json.loads(Path(__file__).with_name('EVEN-LOW-TWIST-WITNESSES.json').read_text())
m=W['m']; T=2399; D=-m; E0=W['base_roots']; E=[D*r for r in E0]
assert E0==[0,-32*T,407] and m==2207
S=[-1,2,3,5,7,11,37,T,m]
L,R=W['cassels_left'],W['cassels_right']; seeds=W['tangent_seeds']
assert L==[11*T,35*T,385] and R==[-74*T,-10*T,185]
def prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def leg(x,p):
    r=pow(x%p,(p-1)//2,p); assert r in (1,p-1)
    return 1 if r==1 else -1
assert all(prime(p)for p in S[1:]) and len(set(S))==len(S)
r0=407*T
assert D%8==r0%8==1
assert [leg(D,p)for p in (3,5,7,11,37,T,61)]==[1,-1,-1,1,-1,1,-1]
assert [leg(r0,p)for p in (3,5,7,61)]==[1,-1,-1,1]
assert all(leg(-E[1],p)==-1 for p in (11,37))
assert leg(-E[2],T)==-1
assert [leg(-E0[1],p)for p in (11,37)]==[-1,1] and leg(-E0[2],T)==-1
assert [leg(D,p)for p in (11,37,T)]==[1,-1,1]
def va(x,p):
    assert x
    a=Q(x);u,v=a.numerator,a.denominator; j=0
    while u%p==0:u//=p;j+=1
    while v%p==0:v//=p;j-=1
    return j
def unit(x,p,n):
    a=Q(x)/Q(p)**va(x,p)
    return a.numerator*pow(a.denominator,-1,p**n)%p**n
def cls(x,p):
    if p==-1:return int(x<0)
    a=va(x,p)%2
    if p==2:return a|({1:0,7:1,5:2,3:3}[unit(x,p,3)]<<1)
    return a|((leg(unit(x,p,1),p)==-1)<<1)
def dot(a,b):
    return (a&b).bit_count()%2
def span(v):
    Y={0}
    for a in v:Y|={z^a for z in Y}
    return Y
def attach(B,r):
    while r:
        j=r.bit_length()-1
        if j in B:r^=B[j]
        else:
            B[j]=r
            return True
    return False
def k3(x,E):
    return [x-r if x!=r else prod(r-z for z in E if z!=r)for r in E]
def enc(values,p,w):
    return cls(values[0],p)|(cls(values[1],p)<<w)

# Dyadic image on E0 (then transport through D's local square).
dyadic=[k3(x,E0)for x in (E0[1],E0[2],E0[1]+640)]
assert all(cls(prod(Z),2)==0 and cls(Z[2],2)==0 for Z in dyadic)
assert span(enc(Z,2,3)for Z in dyadic)=={a|(a<<3)for a in range(8)}
assert all(va(E[i]-E[j],m)==1 for i,j in product(range(3),repeat=2)if i!=j)
assert all(va(E[1]-E[2],p)==e and leg(E[1],p)==c
           for p,e,c in [(3,2,-1),(5,2,1),(7,3,-1)])
Rloc={}; N=len(S); obs={}
for p in S:
    w=1 if p==-1 else 3 if p==2 else 2
    if p in (-1,2):
        B={a|(a<<w)for a in range(1<<w)}
    elif p==3:
        B={x|(y<<2)for x,y in product((0,2),repeat=2)}
    elif p==5:
        B={y<<2 for y in range(4)}
    elif p==7:
        B={0,2<<2,2|(1<<2),2|(3<<2)}
    elif p in (11,37):
        assert va(E[2],p)==1 and va(E[1],p)==0 and leg(-E[1],p)==-1
        B={0,2,1|(2<<2),3|(2<<2)}
    elif p==T:
        assert va(E[1],p)==1 and va(E[2],p)==0 and leg(-E[2],p)==-1
        B={0,2|(2<<2),1|(3<<2),3|(1<<2)}
    else:
        B={0,*[enc(k3(x,E),p,w)for x in E]}
    assert len(B)==1<<w and B==span(B)
    assert all(enc(k3(x,E),p,w)in B for x in E)
    Rloc[p]=sorted(B)
    for f in range(1,1<<(2*w)):
        if any(dot(f,b)for b in B):continue
        r=sum(dot(f,cls(k,p)<<(i*w))<<(i*N+j)
              for i,j in product(range(2),range(N))for k in (S[j],))
        attach(obs,r)
assert len(obs)==14
def encoded(v):
    out=0
    for j,x in enumerate(v[:2]):
        for i,p in enumerate(S):
            if p==-1: e=int(x<0);x=abs(x)
            else:e=va(x,p)%2;x//=p**va(x,p)
            out|=e<<(i+N*j)
        assert x==1
    assert isqrt(prod(v))**2==prod(v) if prod(v)>=0 else False
    return out
basis={}
for row in [k3(E[0],E),k3(E[1],E),L,R]:
    r=encoded(row)
    assert not any(dot(r,v)for v in obs.values()) and attach(basis,r)
assert len(basis)==2*N-len(obs)==4

def root(x,p,k):
    a=va(x,p)
    assert a%2==0 and cls(x,p)==0
    z=unit(x,p,k)
    if p==2:
        r=1
        for j in range(3,k):
            if ((r*r-z)>>j)&1:r+=1<<(j-1)
    else:
        r=next(g for g in range(1,p)if (g*g-z)%p==0)
        M=p;inv=pow(2*r,-1,p)
        for _ in range(1,k):
            r+=M*((z-r*r)//M*inv%p);M*=p
    y=r*Q(p)**(a//2)
    err=va(y*y-x,p)if y*y!=x else 10**9
    slope=va(2*y,p)
    assert err>2*slope
    return y,err-slope
def hilb(x,y,p):
    a=va(x,p);b=va(y,p)
    if p==2:
        v=unit(x,p,3);w=unit(y,p,3)
        return (-1)**(((v-1)*(w-1)//4+a*(w*w-1)//8+b*(v*v-1)//8)%2)
    return (-1)**(a*b*((p-1)//2)%2)*leg(unit(x,p,1),p)**(b%2)*leg(unit(y,p,1),p)**(a%2)

pairs=[(1,2),(2,0),(0,1)]
for (u,v),(B,a,b) in zip(pairs,seeds):
    assert gcd(B,a,b)==1
    assert (E[u]-E[v])*B*B+L[u]*a*a-L[v]*b*b==0
out=[]
for p in S:
    if all(cls(x,p)==0 for x in R):
        out.append([p,1])
        continue
    x=Q(*map(int,W['local_x'][str(p)]))
    if p==-1:
        H=10**35; zs=[]
        for e,l in zip(E,L):
            f=(x-e)/l
            assert f>0
            z=isqrt(f.numerator*H*H//f.denominator)
            assert Q(z*z,H*H)<=f<=Q((z+1)**2,H*H)
            zs.append(Q(z,H))
        row=[]
        for (u,v),(B,a,b),r in zip(pairs,seeds,R):
            tangent=(E[u]-E[v])*B+L[u]*a*zs[u]-L[v]*b*zs[v]
            error=Q(L[u]*abs(a)+L[v]*abs(b),H)
            assert abs(tangent)>error
            row.append(-1 if tangent<0 and r<0 else 1)
        out.append([p,prod(row),[x.numerator,x.denominator],row])
        continue
    zs,acc=zip(*(root(Q(x-e,r),p,70 if p==2 else 18)for e,r in zip(E,L)))
    row=[];k=3 if p==2 else 1
    for (u,v),(B,a,b),r in zip(pairs,seeds,R):
        tangent=(E[u]-E[v])*B+L[u]*a*zs[u]-L[v]*b*zs[v]
        precision=min(va(L[u]*a,p)+acc[u],va(L[v]*b,p)+acc[v])
        assert tangent and precision-va(tangent,p)>=k
        row.append([va(tangent,p),unit(tangent,p,k),hilb(tangent,r,p)])
    out.append([p,prod(r[2]for r in row),[x.numerator,x.denominator],row])
assert [w[0]for w in out if w[1]==-1]==[-1,2,2399]
assert prod(w[1]for w in out)==-1
def count(p):
    assert prime(p) and all((x-y)%p for x,y in zip(E0,E0[1:]+E0[:1]))
    return p+1+sum(leg(Z,p)for x in range(p)
                   for Z in (prod(x-e for e in E0),)if Z%p)
assert (count(61),count(13),count(17))==(68,16,16)
assert leg(r0,13)==-1 and leg(r0,17)==1
assert prod(p+1 for p in (2,3,5,7,11,37,T))==630374400
assert leg(2*2-4*13,17)==-1
assert (61+1-count(61)-(61+1))%17==0
print(json.dumps({'auxiliarly_twisted_roots':E,'Sel2_dimension':4,
                  'global_constraints_rank':len(obs),
                  'finite_local_Kummer_images':Rloc,
                  'actual_Cassels_product':prod(w[1]for w in out),
                  'Cassels_local_rows':out,
                  'inert_cusp_detector_p':61,'aux_split_Heegner_sign':-1,
                  'fixed_base_reduction_order61':count(61),
                  'fixed_base_reduction_order13':count(13),
                  'fixed_base_reduction_order17':count(17),
                  'mod17_Frob13_discriminant_nonsquare':True},indent=2))
