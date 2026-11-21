#!/usr/bin/env python3
from pathlib import Path
from math import gcd, isqrt, prod
import json
HERE=Path(__file__).resolve().parent
rows=json.loads((HERE/'PINNED-POSITIVE-PROFILES.json').read_text())['profiles']
def prime(p):
    return p>1 and all(p%d for d in range(2,isqrt(p)+1))
def leg(a,p):
    r=pow(a%p,(p-1)//2,p)
    assert r in (0,1,p-1)
    return -1 if r==p-1 else r
def local(a,p):
    d=0
    while a%p==0:d,a=d+1,a//p
    return d,a
out=[]
for row in rows:
    eps,ps=row['epsilon'],row['contact_primes']
    assert len(set(ps))==6 and all(prime(p) and p%408==1 and leg(7,p)==-1 for p in ps)
    for i,p in enumerate(ps):
        for j,q in enumerate(ps[i+1:],i+1):
            neg=(eps==-1)^((i,j) in {(1,4),(3,4)})
            assert leg(p,q)==leg(q,p)==1-2*neg
    beta=17*prod(ps)
    j=0
    K=18*beta*2**j
    delta=2*K*K-12*beta
    assert delta>2304*beta
    L,S=delta-1,delta+1
    D,a=S*S,24*L
    A=beta*a*a
    C=D*D-A;B=A+3*D*D
    q,r=D-2*L*L,4*K*L
    assert gcd(A,D)==gcd(q,r)==1
    assert B==3*(q*q+2*r*r)
    assert all(local(A,p)[0]==1 for p in ps)
    local_guards=[]
    for p,e in ((2,6),(3,2),(17,2)):
        depth,u=local(17*A,p)
        assert depth==e and D%p
        assert u%8==1 if p==2 else leg(u,p)==1
        local_guards.append([p,depth,u%(8 if p==2 else p)])
    z=D-288*beta
    assert C-z*z==2304*beta*(delta-36*beta)
    assert z>0 and z*z<C<(z+1)**2 and 0<A<D*D
    out.append(dict(scope='numerical Ready profile, not literal folded source',epsilon=eps,beta=beta,
      contact_primes=ps,j=j,K=K,Delta=delta,L=L,S=S,D=D,A=A,C=C,B_over_3=B//3,
      norm_negative_two=[q,r],ready_local_depths_and_units=local_guards,
      first_coordinate_character='trivial on every actual Sel2 test class by primitive norm and square D'))
print(json.dumps(out,sort_keys=True,indent=2))
