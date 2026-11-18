"""Standalone deterministic checker. No CAS, CM formula, or external certificate service."""
import json,sys
from pathlib import Path
from itertools import product
from fractions import Fraction as F
from math import prod,lcm,gcd
from jacobian import jmul
from overlap import trim
def small_factors(n):
    assert n.bit_length()<=22
    q=2;S=set()
    while q*q<=n:
        while n%q==0:n//=q;S.add(q)
        q+=1
    if n>1:S.add(n)
    return S
def pocklington(C):
    proved=set()
    for n in sorted(map(int,C)):
        v=C[str(n)]
        if n==2:assert v=={};proved.add(n);continue
        a=v['a'];F=v['F'];assert 1<a<n and all(int(q) in proved and k>=1 for q,k in F.items())
        f=prod(int(q)**k for q,k in F.items())
        assert (n-1)%f==0 and f*f>n and pow(a,n-1,n)==1
        assert all(gcd(pow(a,(n-1)//int(q),n)-1,n)==1 for q in F);proved.add(n)
    return proved
def check(P):
    R=json.loads(P.read_text());prime=pocklington(R['prime_certificates'])
    sc=[F(1),F(3134049,4096),F(2825761,4096)];roots=[F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
    d=R['D'];w=R['w'];u=R['u'];assert d==17294016221357051154 and w>0 and u>0
    K=[[-r*d*d/(s*s) for r in roots] for s in sc]
    assert all(k.denominator==1 for row in K for k in row)
    grid=[[u+int(k)*w*w for k in row] for row in K]
    vals=list(dict.fromkeys(sum(grid,[])));assert vals==R['distinct_values'] and len(vals)==13
    inds=[[vals.index(x) for x in row] for row in grid];assert inds==R['grid_indices']
    S=sorted(map(int,R['pairs']));bad={int(k):v for k,v in R['composite_factors'].items()}
    assert sorted(S+list(bad))==list(range(13)) and all(1<g<vals[i] and vals[i]%g==0 for i,g in bad.items())
    bounds={};points={};eligible=[]
    for i in S:
        p=vals[i];assert p in prime and p%816==1 and pow(p%7,3,7)==6
        z,t=R['roots'][str(i)];assert pow(z,8,p)==p-1
        if t is not None:assert pow(t,4,p)==2;eligible.append(i)
        else:assert pow(2,(p-1)//4,p)==p-1
        sr=R['pairs'][str(i)];assert len(sr)==2 and sum(r for r,n in sr)==p
        for j,(r,n) in enumerate(sr):
            assert 0<r<p and r*r%p==2 and n>0
            A=-(3-r)**2%p;pt=(1+r,2*r%p);assert A and (pt[1]**2-pt[0]**3-A*pt[0])%p==0
            bounds[i,j]=n;points[i,j]=(p,A,pt)
    pi=prod(vals[i] for i in S)
    T,G,Q,calls=trim(bounds,lambda k,n:jmul(*points[k],n) is None,pi,16,small_factors)
    assert {str(i):[T[i,0],T[i,1]] for i in S}==R['trimmed']
    sel=R['selected'];bits=R['first_orientation'];h=R['h'];assert len(sel)==len(bits) and set(sel)<=set(S) and set(bits)<={0,1}
    def moduli(U,b):
        return (prod(vals[i] for i in U)**3*lcm(*(T[i,z] for i,z in zip(U,b))),lcm(*(T[i,1-z] for i,z in zip(U,b))))
    m,n=moduli(sel,bits);assert h>0 and h%16==0 and h%m==0 and (h-1)%n==0
    sols={};weighted=0;plain=0
    for s in product((-1,0,1),repeat=len(S)):
        J=tuple(i for i,b in zip(S,s) if b>=0);B=[b for b in s if b>=0]
        if not J:continue
        x,y=moduli(J,B)
        if gcd(lcm(16,x),y)!=1:continue
        weighted=max(weighted,len(J)+2*(0 in J));plain=max(plain,len(J))
        if 0 in J:sols[J]=sols.get(J,0)+1
    maxsize=max(map(len,sols));assert maxsize==R['largest_compatible_with_shared_root']==len(sel)
    assert maxsize>0 and sum(len(J)==maxsize for J in sols)==R['maximal_subsets_count']
    assert sols[tuple(sel)]==R['selected_feasible_orientations']
    return dict(file=P.name,prime_values=len(S),prime_positions=sum(i in S for row in inds for i in row),strong_ray_values=len(eligible),
        max_compatible_distinct_anywhere=plain,max_compatible_positions_anywhere=weighted,selected_positions=[[j,k] for j,row in enumerate(inds) for k,i in enumerate(row) if i in sel],prime_proof_nodes=len(prime),largest_overlap_gcd=max(G),active_primes=Q,scalar_strip_tests=calls,orient_partial_cases=3**len(S),explicit_h_digits=len(str(h)))
if __name__=='__main__':
    D=Path(__file__).resolve().parent;print(json.dumps([check(p) for p in sorted(D.glob('*.json')) if p.name.startswith(('COMPATIBLE','HIGH-PRIME'))],indent=2))
