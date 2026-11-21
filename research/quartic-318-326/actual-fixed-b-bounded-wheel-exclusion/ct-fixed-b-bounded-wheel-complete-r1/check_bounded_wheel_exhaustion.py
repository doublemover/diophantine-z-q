#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import json,re
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
D=Path(__file__).resolve().parent
base=D.parent.parent
infiles=[D/'wheel_literal_donor.cc',D/'EXACT-WHEEL-79.txt',
         D/'JOINED-62-LOCAL-EXCLUSIONS.json',
         base/'joined-work-20261120/linked-detector-fixed-b-small-u-selmer-four-r2/EXACT-LOCAL-258049.json',
         D.parent/'ct-fixed-b-scalar-prefilter-r1/EXACT-SCALAR-GATE-JOINED-CANDIDATES.json',
         D.parent/'ct-fixed-b-two-coordinate-prefilter-r1/EXACT-TWO-COORDINATE-SIX-SURVIVORS.json']
b=10568037907556089;t=F(1,2399);B=8_000_000
data=json.loads(infiles[3].read_bytes());assert data['b']==b
cells=[(p,w,(24+32*w*w)%p) for p,w,_ in data['all_nineteen_local_rows']]
C=sorted([(p,A) for p,w,A in cells])
src=infiles[0].read_text()
assert sorted([(int(p),int(c)) for p,c in re.findall(r'\{([0-9]+),([0-9]+)\}',src)])==C
assert all(p%8==1 and p<2**64 and isprime(p) for p,w,A in cells)
def poly(u,A,p):
    return (16*pow(u,4,p)+A*pow(u,2,p)+1)%p
def chi(a,p):
    z=pow(a%p,(p-1)//2,p);assert z in (0,1,p-1)
    return {0:0,1:1,p-1:-1}[z]
def square_roots_complete(a,p):
    a%=p
    rs=sorted(set(map(int,sqrt_mod(a,p,all_roots=True))))
    assert all(r*r%p==a for r in rs)
    assert len(rs)==(1 if a==0 else 2 if chi(a,p)==1 else 0)
    return rs
def allowed(u):
    return 0<u<=B and u%2 and u%3 and u%17
zeros={}
root_rows=[]
for p,A in C:
    # Quadratic in U²; return complete distinct roots by degree <=4.
    ds=square_roots_complete(A*A-64,p)
    roots=sorted({r for d in ds for r in square_roots_complete((d-A)*pow(32,-1,p),p)})
    assert all(poly(r,A,p)==0 for r in roots) and len(roots)<=4
    root_rows.append([p,A,ds,roots])
    for r in roots:
       for u in range(r,B+1,p):
         if allowed(u):zeros.setdefault(u,[]).append(p)
Z=[dict(u=u,zero_primes=ps,rejecting_prime=next(p for p,A in C if chi(poly(u,A,p),p)==-1))
   for u,ps in sorted(zeros.items())]
assert len(Z)==5
U=list(map(int,infiles[1].read_text().split()))
assert U==sorted(set(U)) and len(U)==79 and all(allowed(u) for u in U)
assert all(all(chi(poly(u,A,p),p)==1 for p,A in C) for u in U)
def vp(x,p):
    x=F(x);n,d=x.numerator,x.denominator;k=0;assert n
    while n%p==0:n//=p;k+=1
    while d%p==0:d//=p;k-=1
    return k
L=[]
for u,kind,p in json.loads(infiles[2].read_bytes()):
    assert allowed(u) and p<2**64 and isprime(p) and p not in (2,3,8912209,1185793321,2399)
    assert chi(b,p)==-1
    la=F(16*u**4+24*u*u+1,32*u*u)
    if kind=='denominator':
        k=vp(la,p)
        assert u%p==0 and k==-2*vp(u,p)<0 and chi(2,p)==-1
        L.append([u,kind,p,k])
    elif kind=='collision':
        k=vp(la+t,p)
        assert k>0 and (k%2 or chi(2399,p)==-1)
        L.append([u,kind,p,k])
    else:raise ValueError(kind)
assert len(L)==62 and len({u for u,*_ in L})==62
sc=json.loads(infiles[4].read_bytes())['cases'];mix=json.loads(infiles[5].read_bytes())['cases']
assert {z['u'] for z in sc if z['status'].startswith('not excluded')}=={z['u'] for z in mix}
assert all(z['status'].startswith(('globally excluded','excluded')) for z in mix)
assert len(sc)==17 and set(U)=={u for u,*_ in L}|{x['u'] for x in sc}
assert not {u for u,*_ in L}&{x['u'] for x in sc}
print(json.dumps(dict(bound=B,raw_wheel_count=len(U),excluded_local_after_wheel=len(L),
  final_affine_exclusions=len(sc),zero_phase_count=len(Z),zero_phase_cases=Z,
  root_rows=root_rows,known_local_exclusion_checks=L,
  source_hashes={p.name:sha256(p.read_bytes()).hexdigest() for p in infiles}),
  sort_keys=True,indent=2))
