#!/usr/bin/env python3
"""Exclude the exact fixed-u retained W balls by an exact affine code."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path
from sympy.ntheory.residue_ntheory import sqrt_mod
import json

D=Path(__file__).resolve().parent
four=D.parent/'ct-fixed-u-258049-one-bit-r1'/'EXACT-ALPHA-FOUR-COVER.json'
cells=D.parent.parent/'joined-work-20261120/linked-detector-fixed-b-small-u-selmer-four-r2/EXACT-LOCAL-258049.json'
digest=lambda p:sha256(p.read_bytes()).hexdigest()
assert digest(four)=='1bafc111ab865a630ede511759c68f9aeee51e254d58cd4dab424bed84a35eb8'
A=json.loads(four.read_bytes()); C=json.loads(cells.read_bytes())
S=A['finite_support']; T=A['normalized_tangent_coefficients']; RS=A['affine_rows']
b=A['b']; t=F(*A['t']); la=F(*A['lambda_']); n=len(S)
assert b==C['b'] and A['case_u']==C['u']==258049 and la==F(*C['Lambda'])
assert len(S)==19 and len(T)==3 and A['affine_dimension']==4

def vp(x,p):
    x=F(x);a,c=x.numerator,x.denominator;v=0
    assert a
    while a%p==0:a//=p;v+=1
    while c%p==0:c//=p;v-=1
    return v,F(a,c)
def residue(x,p):
    x=F(x);return x.numerator*pow(x.denominator,-1,p)%p
def bit(x,p):
    y=pow(residue(x,p),(p-1)//2,p);assert y in (1,p-1)
    return int(y==p-1)
def unit_sqrt(x,p,depth):
    assert vp(x,p)[0]==0
    m=p**depth;x=residue(x,m)
    r=int(sqrt_mod(x%p,p));d=p
    assert (r*r-x)%p==0
    for _ in range(1,depth):
        r+=d*((x-r*r)//d*pow(2*r,-1,p)%p);d*=p
    assert (r*r-x)%m==0
    return r
def dot(a,b):return (a&b).bit_count()%2
def linear_witness(goal,R):
    out=r=0;z=goal
    while z:
        h=z.bit_length()-1
        if h not in R:return None
        m,t,I=R[h];z^=m;r^=t;out^=I
    return r,[j for j in range(len(RS)) if (out>>j)&1]

# Gaussian elimination with original row witnesses, plus complete affine list.
R={}
for j,(z,t0) in enumerate(RS):
    m=z;t0=int(t0);I=1<<j
    while m:
        h=m.bit_length()-1
        if h not in R:
            R[h]=m,t0,I;break
        v,r,J=R[h];m^=v;t0^=r;I^=J
    else:assert not t0
assert len(R)==34
part=A['one_global_twist_mask'];assert all(dot(part,c)==r for c,r in RS)
free=[i for i in range(2*n) if i not in R]
K=[]
for i in free:
    m=1<<i
    for h,(q,_,_) in sorted(R.items()):
        if dot(m,q):m^=1<<h
    assert not any(dot(m,z) for z,r in RS)
    K.append(m)
def classify(m,p):
    mask0=sum(bit(q,p)<<j for j,q in enumerate(S))
    return dot(mask0,m)|(dot(mask0<<n,m)<<2)
def affchoice(J):
    m=part
    for a,k in zip(J,K):
        if a:m^=k
    return m
choices=[affchoice(J) for J in product([0,1],repeat=len(K))]
assert len(set(choices))==16
by_p={int(p):int(w) for p,w,_ in C['all_nineteen_local_rows']}
def actual_ball(p):
    assert p not in S
    w=by_p[p];N=3; rad=(F(w*w)-t)/b;rad2=F(w*w)+la
    y,z=unit_sqrt(rad,p,N),unit_sqrt(rad2,p,N)
    out=[]
    for s,r in product([1,-1],repeat=2):
        v=[w,s*b*y,r*z,1]
        L=[sum(c*q for c,q in zip(R0,v)) for R0 in T]
        assert all(L)
        vs=[vp(x,p)[0] for x in L]
        # Changing W by p² and retaining these signs perturbs every affine
        # Z_i by p², since b, Y, Z are units. Thus each L_i has this
        # deterministic error bound plus the exact p^N root guarantee.
        err=[2+min(vp(x,p)[0] for x in R0[:3] if x) for R0 in T]
        assert all(q<s for q,s in zip(vs,err))
        u=[residue(vp(x,p)[1],p) for x in L]
        d0=(vs[1]+vs[2])%2;d1=(vs[0]+vs[2])%2
        assert d0==d1==0
        code=bit(u[1]*u[2],p)|(bit(u[0]*u[2],p)<<2)
        out.append(dict(signs=[s,r],valuations=vs,error_bounds=err,
                        residue_units=u,code=code))
    glob=sorted({classify(m,p) for m in choices})
    forced=sorted({i['code'] for i in out})
    assert not set(glob)&set(forced)
    mask0=sum(bit(q,p)<<j for j,q in enumerate(S))
    short=[]
    for u,v in ((1,0),(0,1),(1,1)):
        mask=(u*mask0)^(v*(mask0<<n))
        q=linear_witness(mask,R)
        if q is None:continue
        rhs,I=q
        if all((u*(f&1)^v*((f>>2)&1))!=rhs for f in forced):
            # Check this is a direct linear combination of INPUT rows.
            x=check_rhs=0
            for j in I:
                a,r0=RS[j];x^=a;check_rhs^=r0
            assert x==mask and check_rhs==rhs
            short.append(dict(component_bits=[u,v],functional_mask=mask,
                     global_rhs=rhs,input_rows_zero_based=I))
    assert short
    return dict(p=p,W_mod_p2=w,root_precision=N,positive_root_reps=[y,z],
                global_lift_codes=glob,ball_codes=forced,sign_cases=out,
                one_row_certificate=min(short,key=lambda x:len(x['input_rows_zero_based'])))
answer=[actual_ball(p) for p in (52056721,4818481,16688017)]
print(json.dumps(dict(u=258049,b=b,global_affine_rank=len(R),global_lift_count=len(choices),
                      source_sha={four.name:digest(four),cells.name:digest(cells)},
                      separate_one_cell_obstructions=answer),
                 sort_keys=True,indent=2))
