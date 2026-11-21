#!/usr/bin/env python3
"""Necessary scalar Kummer/pushout gate on the old b,t and contact chart.

Rejects rigorously (in the named fixed-b, u-family). A candidate NOT
excluded here need not be ELS, a global point, or a valid original pole.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from functools import cache
from itertools import product
from math import gcd,lcm,prod
from pathlib import Path
import json
from sympy import factorint,isprime
from sympy.abc import x,y,z
from sympy.ntheory.residue_ntheory import sqrt_mod
from sympy.solvers.diophantine.diophantine import diop_ternary_quadratic_normal as solve3

D=Path(__file__).resolve().parent
cells_file=D.parent.parent/'joined-work-20261120/linked-detector-fixed-b-small-u-selmer-four-r2/EXACT-LOCAL-258049.json'
cell_data=json.loads(cells_file.read_bytes())
B=10568037907556089; t=F(1,2399); assert cell_data['b']==B
cells={int(p):int(w) for p,w,_ in cell_data['all_nineteen_local_rows']}
assert len(cells)==19 and all(p<2**64 and isprime(p) for p in cells)
cells_fast=[52056721,4818481]+[p for p in cells if p not in (52056721,4818481)]
known_file=D/'JOINED-LOCAL-PASS-INPUTS.json'
known={int(u): data for u,data in json.loads(known_file.read_bytes())}
primality={}

def vp(v,p):
    v=F(v);n,d=v.numerator,v.denominator;k=0
    assert n
    while n%p==0:n//=p;k+=1
    while d%p==0:d//=p;k-=1
    return k,F(n,d)
def res(u,p):
    u=F(u);return u.numerator*pow(u.denominator,-1,p)%p
def char(u,p):
    x=pow(res(u,p),(p-1)//2,p); assert x in (1,p-1)
    return int(x==p-1)
def loc(v,p):
    k,u=vp(v,p)
    if p==2:return (k%2)*4+{1:0,3:1,5:2,7:3}[res(u,8)]
    return (k%2)*2+char(u,p)
def powp(p,k):
    return F(p**k) if k>=0 else F(1,p**(-k))
def localroot(v,p,N):
    k,u=vp(v,p)
    if k%2 or loc(v,p):return None
    a=res(u,p**N)
    if p==2:
        r=1
        for j in range(3,N):
            if (r*r-a)%2**(j+1):r+=2**(j-1)
        assert (r*r-a)%2**N==0
        return r*powp(p,k//2),k//2+N-1
    r=int(sqrt_mod(a%p,p));P=p
    for _ in range(1,N):
        r+=P*((a-r*r)//P*pow(2*r,-1,p)%p);P*=p
    assert (r*r-a)%P==0
    return r*powp(p,k//2),k//2+N

@cache
def prove_prime(p):
    if p<2**64:
        if not isprime(p):raise ValueError('factor not proven prime')
        return p
    # A fast probable-prime test is only a pre-screen. Successful prime
    # claims above 64 bits require the deterministic certificate below.
    if not isprime(p):raise ValueError('factor failed preliminary prime test')
    # Deterministic Pocklington: partial factor of p−1 is enough.
    # The bounded path refuses unavailable prime proofs.
    F0=1; witnesses=[]
    for q,e0 in sorted(factorint(p-1,limit=100000).items()):
        q,e0=int(q),int(e0)
        try:prove_prime(q)
        except ValueError:continue
        a=next((a for a in range(2,65) if pow(a,p-1,p)==1 and
                        gcd(pow(a,(p-1)//q,p)-1,p)==1),None)
        if a is not None:
            F0*=q**e0;witnesses.append([q,e0,a])
        if F0*F0>p:break
    if F0*F0<=p:raise ValueError('Pocklington prime support unresolved within bound')
    assert (p-1)%F0==0
    primality[p]=witnesses
    return p

def verify_factors(v,rows):
    f={int(p):int(k) for p,k in rows};assert len(f)==len(rows)
    assert all(k>0 for k in f) and prod(p**k for p,k in f.items())==abs(int(v))
    for p in f:prove_prime(p)
    return f

def exact_factors(v,known=(),limit=1000000):
    v=abs(int(v));initial=v;f={}
    for p in known:
        while v%p==0:
            f[p]=f.get(p,0)+1;v//=p
    for p,k in factorint(v,limit=limit).items():
        p=int(p);k=int(k); prove_prime(p); f[p]=f.get(p,0)+k
    assert prod(p**k for p,k in f.items())==initial
    return f
def norm(v):
    D=lcm(*(F(c).denominator for c in v));a=[int(D*c) for c in v]
    e=abs(gcd(*a));return [z//e for z in a]
def ternary_point(coeff,known):
    sf=[];sq=[]
    for n in coeff:
        fac=exact_factors(n,known)
        sf.append((-1 if n<0 else 1)*prod(p for p,j in fac.items() if j%2))
        sq.append(prod(p**(j//2) for p,j in fac.items()))
    g=abs(gcd(*sf)); sf=[n//g for n in sf]
    ps=[abs(gcd(sf[1],sf[2])),abs(gcd(sf[0],sf[2])),abs(gcd(sf[0],sf[1]))]
    ds=[a*h*h//prod(ps) for a,h in zip(sf,ps)]
    assert all(gcd(d,c)==1 for i,d in enumerate(ds) for c in ds[:i])
    out=solve3(ds[0]*x*x+ds[1]*y*y+ds[2]*z*z)
    if not out or any(v is None for v in out) or not any(out):
        raise ValueError('did not certify a rational tangent point')
    R=tuple(map(int,out))
    assert sum(c*a*a for c,a in zip(ds,R))==0
    Q=norm([F(p*h,q) for p,h,q in zip(ps,R,sq)])
    assert gcd(*Q)==1 and sum(c*h*h for c,h in zip(coeff,Q))==0
    return Q

def local_kummer_scalar(p,e):
    # Positive witnesses for the WHOLE first-two tuple image; take the
    # scalar projection only after the exact cardinality is reached.
    need=8 if p==2 else 4
    image={0:None};w=3 if p==2 else 2
    def add_record(u,W):
        l=[loc(q,p) for q in u]
        assert l[0]^l[1]^l[2]==0
        image.setdefault(l[0]|(l[1]<<w),W)
    for i,a in enumerate(e):
        ds=[a-r for r in e]
        ds[i]=prod(d for j,d in enumerate(ds) if j!=i)
        add_record(ds,['torsion',i])
    if len(image)<need:
      for h in sorted(range(-12,13),key=abs):
       for a in e:
        for k in range(1,65):
          if k%p==0:continue
          X=a+k*powp(p,h)
          ds=[X-r for r in e]
          if not all(ds):continue
          u=[loc(q,p) for q in ds]
          if u[0]^u[1]^u[2]==0:
            add_record(ds,[X.numerator,X.denominator])
          if len(image)==need:break
        if len(image)==need:break
       if len(image)==need:break
    if len(image)!=need:return None
    return sorted({v>>w for v in image})

def alpha_offset(p,e,L):
    # g1= L0*L2/H², H=1. Uniformly bounded sample; absence is unknown.
    prec=18
    for h in sorted(range(-12,13),key=abs):
      for a in e:
       for k in range(1,65):
        if k%p==0:continue
        X=a+k*powp(p,h)
        rr=[(X-d)/e0 for d,e0 in zip(e,[B,1,B])]
        if not all(rr) or any(loc(q,p) for q in rr):continue
        rt=[localroot(q,p,prec) for q in rr]
        assert all(rt)
        U=[q[0] for q in rt]+[F(1)];N=[q[1] for q in rt]
        v=[sum(c*r for c,r in zip(l,U)) for l in L]
        margin=[min(vp(c,p)[0]+n for c,n in zip(l,N) if c) for l in L]
        if all(q and r>=vp(q,p)[0]+(3 if p==2 else 1) for q,r in zip(v,margin)):
            return loc(v[0]*v[1],p)
    return None

def combination_mask(row,number):
    x=0
    for i,k in enumerate(row):
        if number>>i&1:x^=k
    return x

def candidate(U):
    assert U>0 and U%2 and U%3 and U%17 and U <= 8_000_000
    la=F(16*U**4+24*U*U+1,32*U*U)
    # Do the nineteen genuinely cheapest local residue guards before factorization.
    unclear=[]
    for p in cells_fast:
      W=F(cells[p]); s=(W*W-t)/B;z2=W*W+la
      if U%p==0:unclear.append(p);continue
      # For p not dividing b, nonzero mod p radii are enough for exact necessity.
      if B%p or vp(W*W-t,p)[0]==1:
        for i,q in enumerate((s,z2)):
          if q and vp(q,p)[0]==0 and char(q,p)==1:
            return dict(status='excluded local contact square',u=U,p=p,failed_coordinate=i,
                        exact_unit_residue=res(q,p))
      else:unclear.append(p)
    try:
      z0=known.get(U)
      if z0:
        assert la==F(*z0['lambda_']) and la+t==F(*z0['lambda_plus_t'])
        fs=[verify_factors(n,z0[k]) for n,k in
             ((U,'u_factor'),(la.numerator,'lambda_factor'),((la+t).numerator,'lambda_plus_t_factor'))]
      else:fs=[exact_factors(n) for n in (U,la.numerator,(la+t).numerator)]
      S=sorted({2,2399,8912209,1185793321,*(p for f in fs for p in f)})
      G=[-1,*S];w=len(G)
      cs0=norm([F(1),-B,B*(la+t)])
      p0=ternary_point(cs0,S)
    except (ValueError,TypeError,ArithmeticError) as exc:
      return dict(status='unknown arithmetic factorization or conic',u=U,reason=str(exc))
    cs2=norm([F(B),-1,-B*t]);p2=[4619710060,B*41,2399*38613147]
    assert sum(c*v*v for c,v in zip(cs2,p2))==0
    L=[[0,cs0[0]*p0[0],cs0[1]*p0[1],cs0[2]*p0[2]],
       [cs2[0]*p2[0],cs2[1]*p2[1],0,cs2[2]*p2[2]]]
    e=[F(0),B*t,-B*la]
    rows=[];piv={};skipped=[]
    for p in S:
      im=local_kummer_scalar(p,e)
      if im is None:skipped.append([p,'unproved exact scalar image']);continue
      if len(im)==(8 if p==2 else 4):continue
      off=alpha_offset(p,e,L)
      if off is None:skipped.append([p,'no certified reference in search bound']);continue
      h=[loc(g,p) for g in G]
      for j in range(1,8 if p==2 else 4):
        if any((v&j).bit_count()%2 for v in im):continue
        c=sum(((v&j).bit_count()%2)<<i for i,v in enumerate(h));r=(off&j).bit_count()%2
        idx=len(rows);rows.append([p,j,c,r,off,im]);z0=c;s0=r;mark=1<<idx
        while z0:
          j0=z0.bit_length()-1
          if j0 not in piv:piv[j0]=(z0,s0,mark);break
          z1,s1,mark1=piv[j0];z0^=z1;s0^=s1;mark^=mark1
        else:
          if s0:
            cm=cr=0
            for j2,row in enumerate(rows):
              if mark>>j2&1:cm^=row[2];cr^=row[3]
            assert cm==0 and cr==1
            return dict(status='excluded global scalar affine compatibility',u=U,
                tangent_seed0=p0,scalar_tangent_forms=L,
                signed_support=G,rows=rows,input_mask=mark,skipped=skipped)
    for p in cells_fast:
      if p in S:continue  # first scalar gate only uses good retained cells
      if p in unclear:continue
      W=F(cells[p]);v=[(W*W-t)/B,W*W+la]
      if any(not q or vp(q,p)[0]!=0 or loc(q,p) for q in v):continue
      roots=[localroot(q,p,3)[0] for q in v];Zbits=[]
      er=[2+min(vp(r,p)[0] for r in l[:3] if r) for l in L]
      for sg,sh in product([1,-1],repeat=2):
        Us=[W,B*sg*roots[0],sh*roots[1],F(1)]
        v=[sum(c*q for c,q in zip(l,Us)) for l in L]
        if any(not q or vp(q,p)[0]>=k for q,k in zip(v,er)):break
        if vp(v[0]*v[1],p)[0]%2:break   # no unexpected odd valuation used
        Zbits.append(char(vp(v[0]*v[1],p)[1],p))
      if len(Zbits)!=4 or len(set(Zbits))!=1:continue
      goal=sum(char(g,p)<<i for i,g in enumerate(G));z0=goal;s0=0;mark=0
      while z0:
        j=z0.bit_length()-1
        if j not in piv:break
        z1,s1,mark1=piv[j];z0^=z1;s0^=s1;mark^=mark1
      if not z0 and s0!=Zbits[0]:
        z1=s1=0
        for i,row in enumerate(rows):
          if mark>>i&1:z1^=row[2];s1^=row[3]
        assert z1==goal and s1==s0
        return dict(status='excluded by one scalar and one original contact ball',u=U,p=p,
          W_mod_p2=cells[p],tangent_seed0=p0,scalar_tangent_forms=L,signed_support=G,
          global_forced_bit=s0,ball_sign_bits=Zbits,scalar_affine_rows=rows,
          constraint_functional=goal,input_mask=mark,skipped=skipped)
    return dict(status='not excluded by selected scalar tests; NO existence or rank conclusion',
      u=U,scalar_row_count=len(rows),rank=len(piv),skipped=skipped)

def main():
    ap=ArgumentParser();ap.add_argument('u',type=int,nargs='+')
    args=ap.parse_args()
    print(json.dumps(dict(donor_sha256=sha256(cells_file.read_bytes()).hexdigest(),
        joined_passthrough_sha256=sha256(known_file.read_bytes()).hexdigest(),
        cases=[candidate(u) for u in args.u],pocklington_certificates=primality),indent=2,sort_keys=True))
if __name__=='__main__':main()
