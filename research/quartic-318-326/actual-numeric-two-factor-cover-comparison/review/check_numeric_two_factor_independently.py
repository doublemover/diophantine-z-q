#!/usr/bin/env python3
"""Independent F2 rank reconstruction and finite Cassels witness evaluation."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import gcd, prod
import json,sys
pdir=Path(sys.argv[1])
SUP=(2,3,5,7,11,37,2399)
PA,QA=415721,163199081
PR=((7497601,25515769),(16990081,17238721))

def vp_unit(x,p):
    x=F(x); v=0
    if not x:return float('inf'),F(0)
    while x.numerator%p==0:x/=p;v+=1
    while x.denominator%p==0:x*=p;v-=1
    return v,x
def mod(x,m):
    x=F(x); return x.numerator*pow(x.denominator,-1,m)%m
def jac(a,n):
    s=1; a%=n
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5):s=-s
        if a%4==n%4==3:s=-s
        a,n=n%a,a
    return s if n==1 else 0
def bits(x,p):
    assert x
    if p==-1:return int(x<0)
    v,u=vp_unit(x,p)
    if p==2:
        z=mod(u,8)
        return (v%2)|(((z-1)//2)%2<<1)|(((z*z-1)//8)%2<<2)
    nz=jac(mod(u,p),p)
    assert nz
    return (v%2)|(int(nz==-1)<<1)
def hs(x,y,p):
    u,v=bits(x,p),bits(y,p)
    bit=lambda n,i:(n>>i)&1
    if p==2:
        return (-1)**(bit(u,1)*bit(v,1)+bit(u,0)*bit(v,2)+bit(u,2)*bit(v,0))
    return (-1)**((p//2)*bit(u,0)*bit(v,0)+bit(u,1)*bit(v,0)+bit(u,0)*bit(v,1))
def pair(d,p,m):
    c=tuple(bits(x,p) for x in d)
    if len(c)==3:assert c[0]^c[1]^c[2]==0
    return c[0]|c[1]<<m
def rank(rows):
    piv={}
    for x in rows:
        while x:
            a=x.bit_length()-1
            if a not in piv:
                piv[a]=x;break
            x^=piv[a]
    return len(piv)
def dot(x,y):return (x&y).bit_count()%2
def choices(D,p):
    """Exact local images from proved odd cluster criteria, literal torsion,
    or explicit dyadic square coordinates; encode first two squareclasses."""
    S=-32*407*2399**2*D; T=2399*407**2*D
    E=(0,S,T)
    if p==-1:return [0,1]
    if p==2:
        assert vp_unit(S,p)[0]==5 and mod(S//32,8)==1 and mod(T,8)==7
        x=S+640
        assert bits(x,2)==bits(x-S,2)==bits(10,2) and bits(x-T,2)==0
        assert bits(S,2)==2**0 and bits(S*(S-T),2)==2**0
        assert bits(S*T,2)==bits(-S,2)==bits(-2,2)
        return [i|i<<3 for i in range(8)]
    if p in (3,5,7):
        d=vp_unit(T-S,p)[0]
        assert d==({3:2,5:2,7:3})[p] and bits(S,p)==({3:2,5:0,7:2})[p]
        if p==3:return [i|j<<2 for i,j in product([0,2],repeat=2)]
        if p==5:return [i<<2 for i in range(4)]
        return [0,8,6,14]  # v=(0,1,1) iff first unit is nonsquare
    ans=[0]
    for i in range(3):
        d=[E[i]-x for x in E]
        d[i]=prod(x for j,x in enumerate(d) if j!=i)
        ans.append(pair(d,p,2))
    # Four distinct valuation pairs. Hence these are all local images.
    assert {v&5 for v in ans}=={0,1,4,5}
    return ans
summary=[]
for n,(q1,q2) in enumerate(PR,1):
    exact=json.loads((pdir/f'EXACT-NUMERIC-CASSELS-{n}.json').read_text())
    xjson=json.loads((pdir/f'EXACT-NUMERIC-SEL2-{n}.json').read_text())
    old=json.loads((pdir/f'EXACT-TWO-FACTOR-LOCAL-{n}.json').read_text())
    a,b=PA*QA,q1*q2; D=a*b
    assert exact['D']==xjson['D']==old['D']==D
    assert all(bits(a,p)==bits(b,p)==0 for p in SUP) and bits(b,23)==2
    P=(-1,2,5,7,11,37,2399,PA,QA,q1)
    M=(D,b,a)
    Fv=(2399,7*11*37*2399*a,7*11*37*a)
    U=(2399*a*q1,2399*q1,a)
    V=(11,5*2399,5*11*2399)
    B=(Fv,U,V)
    tests=[-1,*SUP,PA,QA,q1,q2]
    # Two independent Kummer coordinates, 2*len(P) unknowns. Orthogonal
    # functionals to each exact local subgroup give all constraints.
    eqns=[]
    for p in tests:
        m=1 if p==-1 else 3 if p==2 else 2
        im=choices(D,p) if p!=q2 else [0]
        for C in B:assert pair(C,p,m) in im,(n,p,C)
        aL=[bits(q,p)<<(loc*m) for loc,q in product(range(2),P)]
        eqns.extend(sum(dot(u,v)<<i for i,v in enumerate(aL))
                    for u in range(1,1<<(2*m)) if all(not dot(u,v) for v in im))
    rk=rank(eqns)
    assert rk==17 and len(B)==3
    # Independent global pivot sources: only U has q1 in its first entry,
    # only V has 11 in the first entry, and then F has 2399.
    assert all(rank([sum(bool(t[0]%p==0)<<i for i,p in enumerate((q1,11,2399))) for t in B])==3 for _ in [0])
    assert pair(M,q2,2)==choices(D,q2)[3]
    e=(0,F(-32*D,407),F(D,2399))
    # Verify actual finite Hensel witnesses and polar evaluations.
    pairing=[]
    for row,d,w in zip(exact['rows'],(M,M,U),(U,V,V),strict=True):
        hits=[]
        Bmat=[]
        assert row['first']==list(d) and row['second']==list(w)
        for i,(_,j,k,coef,src) in enumerate(row['tangents']):
            assert [j,k]==[u for u in range(3) if u!=i] and gcd(*coef)==gcd(*src)==1
            lam=F(coef[0],d[j])
            assert lam and coef==[lam*d[j],-lam*d[k],lam*(e[j]-e[k])]
            assert sum(t*x*x for t,x in zip(coef,src))==0
            Bmat.append(tuple(F(t*x) for t,x in zip(coef,src)))
        assert [l for l,_,_ in row['local_rows']]==[2,3,5,7,11,13,17,19,23,29,37,2399,PA,QA,q1,q2]
        for p,z,dat in row['local_rows']:
            if dat is None:
                assert all(bits(v,p)==0 for v in w)
                s=1
            else:
                ax=F(*dat['x']); R=list(map(lambda y:F(*y),dat['z']))
                prec=[]
                for i,g in enumerate(R):
                    ri=(ax-e[i])/d[i]
                    Vg=vp_unit(g,p)[0]; Dg=vp_unit(2*g,p)[0]
                    se=vp_unit(g*g-ri,p)[0]
                    assert g and se>2*Dg
                    prec.append(se-Dg)
                factors=[]
                for i,(l,m,c) in enumerate(Bmat):
                    j,k=tuple(u for u in range(3) if u!=i)
                    L=l*R[j]+m*R[k]+c
                    assert min(vp_unit(l,p)[0]+prec[j],vp_unit(m,p)[0]+prec[k])>=vp_unit(L,p)[0]+(1 if p!=2 else 3)
                    assert L==F(*dat['tans'][i])
                    factors.append(hs(L,w[i],p))
                assert factors==dat['sy']
                s=prod(factors)
            assert s==z
            if s<0:hits.append(p)
        z=(-1)**len(hits)
        assert z==row['total']
        pairing.append((row['name'],hits,z))
    assert [z for _,_,z in pairing]==([-1,-1,-1] if n==1 else [1,1,-1])
    summary.append(dict(variant=n,D=D,normalized_support_bits=2*len(P),Kummer_rank=rk,normalized_Sel2_dimension=2*len(P)-rk,Cassels=pairing,
                        p23_squareclass_b=bits(b,23),archived_old_cells=len(old['old_cells_W_a_unit_b_unit'])))
print(json.dumps(summary,indent=2))
