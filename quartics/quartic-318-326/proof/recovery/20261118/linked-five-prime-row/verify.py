"""Stdlib Lucas prime certificates, Jacobian R-order check, exact original-row CRT."""
from pathlib import Path
from math import prod,lcm,gcd
from fractions import Fraction as F
from itertools import product
import json
HERE=Path(__file__).resolve().parent
def verifyPrimeTree(c):
    ok=set()
    for n in sorted(map(int,c)):
        row=c[str(n)]
        if n==2:assert row=={};ok.add(2);continue
        a=row['a']; f=row['p_minus_one']
        assert n>2 and 1<a<n and all(int(q) in ok and k>0 for q,k in f.items())
        assert prod(int(q)**k for q,k in f.items())==n-1 and pow(a,n-1,n)==1
        assert all(gcd(pow(a,(n-1)//int(q),n)-1,n)==1 for q in f)
        ok.add(n)
    return ok

def jmul(p,A,pt,n):
    O=(1,1,0)
    def dbl(P):
        X,Y,Z=P
        if not Y or not Z:return O
        yy=Y*Y%p;s=4*X*yy%p;m=(3*X*X+A*pow(Z,4,p))%p
        x=(m*m-2*s)%p
        return x,(m*(s-x)-8*yy*yy)%p,2*Y*Z%p
    def mixed(P,Q):
        X,Y,Z=P;x,y=Q
        if Z==0:return (x,y,1)
        z2=Z*Z%p;u=x*z2%p;v=y*z2*Z%p
        h=(u-X)%p;r=(v-Y)%p
        if h==0:return dbl(P) if r==0 else O
        h2=h*h%p;h3=h2*h%p;bh=X*h2%p
        xx=(r*r-h3-2*bh)%p
        return xx,(r*(bh-xx)-Y*h3)%p,Z*h%p
    R=O
    for b in bin(n)[2:]:
        R=dbl(R)
        if b=='1':R=mixed(R,pt)
    x,y,z=R
    if z==0:return None
    iz=pow(z,-1,p)
    return [x*iz**2%p,y*iz**3%p]
def main(path):
    r=json.loads(path.read_text());pp=verifyPrimeTree(r['prime_proofs']);D=r['D'];w=r['w'];u=r['u'];vals=r['primes']
    roots=[F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
    sc=([F(1),F(3134049,4096),F(2825761,4096)] if path.name.startswith('SHARED') else [F(1)])
    grid=[[F(u)-x*(D*w)**2/t**2 for x in roots] for t in sc]
    assert all(v.denominator==1 for row in grid for v in row) and list(map(int,grid[0]))==vals[:5]
    cover=path.name=='SHARED-COVERAGE.json'; count=6 if cover else 5
    assert len(vals)==len(r['data'])==len(r['roots'])==count and len(set(vals))==count
    if cover:
        divs=[[0]*5,[0,101,19,163,23],[0,41,83,0,2777]]
        ind=[]; slots=[]
        for j,row in enumerate(grid):
            for k,v in enumerate(row):
                n=int(v);g=divs[j][k]
                if g: assert 1<g<n and n%g==0;continue
                ind.append(vals.index(n));slots.append((j,k))
        assert ind==r['position_indices'] and len(ind)==8
    else:ind=list(range(5))
    
    pairs=[]
    for p,pair,(z,t) in zip(vals,r['data'],r['roots']):
        assert p in pp and pow(z,8,p)==p-1 and pow(t,4,p)==2 and p not in (2,3,7)
        if path.name.startswith('SHARED'):assert p%816==1 and pow(p%7,3,7)==6
        assert len(pair)==2 and sum(o['sqrt2'] for o in pair)==p
        ns=[]
        for o in pair:
            x=o['sqrt2']; n=o['order'];A=-(3-x)**2%p
            T=((1+x)%p,2*x%p)
            assert 0<x<p and x*x%p==2 and A and (T[1]**2-T[0]**3-A*T[0])%p==0
            f=o['factors'];assert n>0 and all(int(q) in pp and k>0 for q,k in f.items()) and prod(int(q)**k for q,k in f.items())==n
            assert jmul(p,A,T,n) is None and set(o['drops'])==set(f)
            for q in f:
                v=jmul(p,A,T,n//int(q))
                assert v is not None and v==o['drops'][q]
            ns.append(n)
        pairs.append(ns)
    pairs=[pairs[i] for i in ind];pi=prod(vals);solutions=[]
    for bits in product([0,1],repeat=len(pairs)):
        mm=lcm(*(n[b] for n,b in zip(pairs,bits)));mp=lcm(*(n[1-b] for n,b in zip(pairs,bits)))
        a=pi**3*mm
        if gcd(lcm(a,16),mp)==1:solutions.append((bits,mm,mp))
    if cover and r['bits'] is None:
        assert not solutions
        return dict(file=path.name,prime_value_positions=slots,distinct_prime_values=count,
          exact_composite_positions=7,prime_tree_nodes=len(pp),order_certificates=2*count,
          eight_prime_position_orientations_tested=2**len(ind),compatible_orientations=0)
    bits=tuple(r['bits']);assert (bits,r['minus'],r['plus']) in solutions
    h,period=r['crt']
    assert 0<=h<period and h%(pi**3*r['minus'])==0 and (h-1)%r['plus']==0 and h%16==0
    assert period==lcm(pi**3*r['minus'],r['plus'],16)
    return dict(file=path.name,degree_of_coverage="5 positions, not 15",prime_tree_nodes=len(pp),order_certificates=len(pairs)*2,
      orientation_solutions_with_L16_h0zero=len(solutions),valid_bits=bits,all_p_mod_816=[p%816 for p in vals])
if __name__=='__main__':print(json.dumps([main(p) for p in sorted(p for p in HERE.glob('*.json') if p.name in ('ROW-SPECIFIC.json','SHARED-CLEARING-ROW.json','SHARED-COVERAGE.json'))],indent=2))
