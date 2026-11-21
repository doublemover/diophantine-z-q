#!/usr/bin/env python3
"""Recover one actual composite ideal of prescribed norm without factoring it."""
from pathlib import Path
from math import gcd, isqrt
import contextlib, hashlib, io, json, runpy
import sympy as s
H=Path(__file__).resolve().parent
def donor(path, sha):
    p=H.parent/path
    assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
    return p
p=donor('actual-one-I-principal-relation-r1/EXACT-FIRST-PRINCIPAL-DIVISOR.json',
        '0fc655687e1eac9a2ef192445eefcbef7d092c16c8e75e8bd7e29a5dd205e3e3')
dct=json.loads(p.read_bytes());C=dct['remaining_cofactor_unfactored'];d=dct['d']
assert gcd(C,6*13*5881*d)==1
src=H.parent/'actual-one-I-cyclotomic13-r1'/'check_point_field13_presentation.py'
raw=src.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='ba77f4e59b1bc81357e44a93628104d1510fef911cdc5fe247d998ec1f8c2a76'
with contextlib.redirect_stdout(io.StringIO()) as out:
    mod=runpy.run_path(str(src))
assert hashlib.sha256(out.getvalue().encode()).hexdigest()=='7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a'
X=mod['u']; G=mod['g']; Z=mod['Z']; psi=mod['psi']; f=mod['f']
B_num=Z(X);B_den=Z(1)
for k in range(2,7):
    a,b=mod['mul'](psi(k),psi(k));c,e=mod['mul'](psi(k-1),psi(k+1))
    assert not b and not e
    y_num=X*a-c;y_den=a
    g=y_num.gcd(y_den)
    y_num=y_num.exquo(g);y_den=y_den.exquo(g)
    B_num=B_num*y_den+y_num*B_den;B_den=B_den*y_den
    g=B_num.gcd(B_den)
    B_num=B_num.exquo(g);B_den=B_den.exquo(g)
B_den*=2
w=B_num**2-d*G*B_den**2
assert B_den.degree()>0 and w.degree()>f.degree()

class Pivot(Exception):
    def __init__(self,a,N):
        self.z=gcd(a,N)
        assert 1<self.z<N

def mcoeff(v,N):
    a=[int(x)%N for x in v]
    while a and a[0]==0:a.pop(0)
    return a

def mmonic(v,N):
    v=mcoeff(v,N)
    if not v:return []
    a=v[0]
    if gcd(a,N)>1:raise Pivot(a,N)
    z=pow(a,-1,N)
    return [z*x%N for x in v]

def mrem(f,g,N):
    assert g and g[0]==1
    X=f[:]
    p=max(0,len(X)-len(g)+1)
    g=g[1:]
    for i in range(p):
        a=X[i]
        if a:
            for j,b in enumerate(g,i+1):X[j]=(X[j]-a*b)%N
    return mcoeff(X[p:],N)

def mgcd(a,b,N):
    a=mmonic(a,N);b=mmonic(b,N)
    while b:
        a,b=b,mmonic(mrem(a,b,N),N)
    return a

def ev(a,x,N):
    y=0
    for z in a:y=(y*x+int(z))%N
    return y

def split_pivot(N,factor):
    G=factor
    while True:
        h=gcd(N,G*G)
        if h==G:break
        G=h
    assert 1<G<N and gcd(G,N//G)==1,(len(str(G)),len(str(N)))
    return G,N//G

def solve(N):
    try:
        g=mgcd(f.all_coeffs(),w.all_coeffs(),N)
        if len(g)!=2:return [dict(N=N,status='nonlinear',common_degree=len(g)-1)]
        u=-g[1]%N
        den=ev(B_den.all_coeffs(),u,N)
        if gcd(den,N)>1:raise Pivot(den,N)
        b=ev(B_num.all_coeffs(),u,N)*pow(den,-1,N)%N
        v=13*u%N;W=169*b%N
        assert ev(f.all_coeffs(),u,N)==0
        assert ev(f.diff().all_coeffs(),u,N)%N!=0 and gcd(N,ev(f.diff().all_coeffs(),u,N))==1
        assert (W*W-13*d*v*(v-13)*(v+39))%N==0 and gcd(W,N)==1
        assert gcd(N,ev(B_den.all_coeffs(),u,N))==1
        return [dict(N=N,status='linear',u=u,B=b,v=v,W=W)]
    except Pivot as e:
        A,B=split_pivot(N,e.z)
        return solve(A)+solve(B)

assert all(5881%m for m in range(2,isqrt(5881)+1))
small=solve(5881)
assert small==[dict(N=5881,status='linear',u=2185,B=2421,v=4881,W=3360)]
larger=solve(C)
assert all(r['status']=='linear' for r in larger), [(r['status'],len(str(r['N']))) for r in larger]
assert len(larger)==1 and larger[0]['N']==C
assert pow(C,4,53)==13  # C cannot be a rational integer 13th power
assert all(gcd(r['N'],t['N'])==1 for i,r in enumerate(larger) for t in larger[:i])
print(json.dumps(dict(same_actual_d=d,small5881=small[0],unfactored_cofactor_ideals=larger,
   poly_degrees=[B_num.degree(), B_den.degree(), w.degree()],
   cofactor_non_13th_power_witness=dict(p=53, residue=C%53, power4=pow(C,4,53)),
   exact_prior_norm_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
   exact_donor_script_sha256=hashlib.sha256(raw).hexdigest()),sort_keys=True,indent=2))
