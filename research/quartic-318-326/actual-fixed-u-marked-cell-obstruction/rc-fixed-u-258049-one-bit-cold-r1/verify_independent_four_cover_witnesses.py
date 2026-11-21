"""Audit archived witnesses without repeating the source's affine solve or point search."""
from fractions import Fraction as Q
from hashlib import sha256
from math import gcd,log2,prod
from pathlib import Path
from sys import argv
import json
raw=Path(argv[1]).read_bytes()
assert sha256(raw).hexdigest()=='1bafc111ab865a630ede511759c68f9aeee51e254d58cd4dab424bed84a35eb8'
data=json.loads(raw)
k0,k1=data['one_global_twist_xi']; b=data['b']; u=data['case_u']
t,lam=Q(*data['t']),Q(*data['lambda_'])
assert b==8912209*1185793321 and u==258049 and t==Q(1,2399) and lam==Q(16*u**4+24*u*u+1,32*u*u)
e=[Q(0),b*t,-b*lam]; d=[b,1,b]
L=data['normalized_tangent_coefficients']; S=data['finite_support']
def integral_valuation(k,p):
    assert k
    v=0
    while k%p==0:
        k//=p
        v+=1
    return v,k
def local(q,p):
    vn,n=integral_valuation(q.numerator,p)
    vd,d=integral_valuation(q.denominator,p)
    return vn-vd,Q(n,d)
def v(q,p):
    return local(q,p)[0]
def belongs_den(q):
    n,d=abs(q.numerator),q.denominator
    assert n
    for p in S[1:]:
        while n%p==0:n//=p
        while d%p==0:d//=p
    return n==d==1
def sq_u(q,p):
    e,a=local(q,p)
    if e%2:return False
    m=8 if p==2 else p
    t=a.numerator*pow(a.denominator,-1,m)%m
    return t==1 if p==2 else pow(t,(p-1)//2,p)==1
assert S[0]==-1 and len(S)==19 and list(sorted(set(S)))==S
assert all(belongs_den(q) for q in map(Q,[*d,k0,k1,*[x-y for i,x in enumerate(e) for y in e[:i]]]))
i,j,k,C,z=data['third_conic_seed']
assert (i,j,k)==(0,1,2) and gcd(*z)==1 and sum(c*x*x for c,x in zip(C,z))==0
assert [Q(c,C[0]) for c in C]==[1,-b,e[1]-e[2]]
assert L[i]==[0,*[c*x for c,x in zip(C,z)]]
# Recheck archived row rank by explicit Boolean elimination in the opposite column order.
M=[[(x>>j)&1 for j in range(38)]+[y] for x,y in data['affine_rows']]
rank=0
for j in range(38):
    r=next((r for r in range(rank,len(M)) if M[r][j]),None)
    if r is None:continue
    M[r],M[rank]=M[rank],M[r]
    for j2 in range(rank+1,len(M)):
        if M[j2][j]:
            M[j2]=[x^y for x,y in zip(M[j2],M[rank])]
    rank+=1
assert rank==34 and not any(row[-1] for row in M[rank:])
assert len(data['exact_local_affine_memberships'])==len(S)
out=[]
for p in S:
    w=data['exact_local_affine_memberships'][str(p)]['direct_lift_witness']
    x=Q(*w['x']); z=[Q(*k) for k in w['roots']]
    a=[(x-r)/dn for r,dn in zip(e,d)]
    prec=w['root_precisions']
    assert z[3]==1 and all(z) and all(a)
    vals=[sum(c*x for c,x in zip(row,z)) for row in L]
    assert vals==[Q(*r) for r in w['tangent_values']] and all(vals)
    if p==-1:
        for q,r,n in zip(a,z,prec):
            assert abs(r)**2<=q< (abs(r)+Q(1,2**n))**2
        assert all(abs(y)>sum(abs(c)*Q(1,2**n) for c,n in zip(row,prec)) for y,row in zip(vals,L))
        assert vals[1]*vals[2]*k0>0 and vals[0]*vals[2]*k1>0
    else:
        h=int(p==2)
        for q,r,n in zip(a,z,prec):
            assert n>v(r,p)+h
            err=r*r-q
            assert not err or v(err,p)>=n+v(r,p)+h
        for y,row in zip(vals,L):
            assert min(v(Q(c),p)+n for c,n in zip(row,prec) if c)>=v(y,p)+(3 if p==2 else 1)
        assert sq_u(vals[1]*vals[2]/k0,p) and sq_u(vals[0]*vals[2]/k1,p)
    out.append(p)
print(json.dumps(dict(affine_rank=rank,independent_direct_witnesses=out),indent=2))
