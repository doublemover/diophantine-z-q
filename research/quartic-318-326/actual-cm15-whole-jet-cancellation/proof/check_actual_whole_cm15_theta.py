#!/usr/bin/env python3
"""Whole signed ramified X_0(32)/F_5 shell, fixed frame across actual C_32.
Two independent geometric donors: actual 16 marked q-normalized differential
table, and prior CM15 two-class j/lift calculation (assertions below).
"""
from __future__ import annotations
from itertools import product
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import argparse
import json

pa = argparse.ArgumentParser()
pa.add_argument('labels_file', type=Path)
pa.add_argument('--q', type=int, nargs='+', default=[1,17,41,89,193,257,2113,3881])
args = pa.parse_args()
raw = args.labels_file.read_bytes()
src = json.loads(raw)
assert len(src['basis_vertices']) == 16
assert sha256(raw).hexdigest()=="9bca1a93b749cdf3f2e5163c31953ac5a3cac88240f2cceb475246bd33f9d0d8"

def dec(i):
    return (i%5,i//5)

def enc(a,b=0):
    return a%5+5*(b%5)

def ad(i,j):
    a,b=dec(i)
    c,d=dec(j)
    return enc(a+c,b+d)

def mu(i,j):
    a,b=dec(i)
    c,d=dec(j)
    return enc(a*c+2*b*d,a*d+b*c)

ADD=[[ad(i,j) for j in range(25)] for i in range(25)]
MUL=[[mu(i,j) for j in range(25)] for i in range(25)]
ROOT=enc(2,1)
MOD=5**16
class K:
    """k(t), t^8=2+rho, k=F25, rho²=2."""
    __slots__=('c',)
    def __init__(self,c=0):
        self.c=(enc(c),)+(0,)*7 if isinstance(c,int) else tuple(c)
    @staticmethod
    def base(a,b=0):
        return K((enc(a,b),)+(0,)*7)
    @staticmethod
    def cv(o):
        return o if isinstance(o,K) else K(o)
    def __add__(a,b):
        return K(ADD[i][j] for i,j in zip(a.c,a.cv(b).c))
    __radd__=__add__
    def __neg__(a):
        return K(MUL[4][x] for x in a.c)
    def __sub__(a,b):
        return a+-a.cv(b)
    def __rsub__(a,b):
        return a.cv(b)+-a
    def __mul__(a,b):
        b=a.cv(b)
        if not any(b.c[1:]): return K(MUL[b.c[0]][x] for x in a.c)
        if not any(a.c[1:]): return K(MUL[a.c[0]][x] for x in b.c)
        r=[0]*8
        for i,x in enumerate(a.c):
            if not x: continue
            for j,y in enumerate(b.c):
                if not y: continue
                val=MUL[x][y]; k=i+j
                if k>=8: k-=8; val=MUL[val][ROOT]
                r[k]=ADD[r[k]][val]
        return K(r)
    __rmul__=__mul__
    def __pow__(a,e):
        if e<0:
            return a.inv()**(-e)
        z=K(1)
        while e:
            if e%2:z=z*a
            e//=2
            if e:a=a*a
        return z
    def inv(a):
        assert a
        if not any(a.c[1:]):
            j=next(j for j in range(1,25) if MUL[a.c[0]][j]==1)
            return K([j,0,0,0,0,0,0,0])
        return a**(MOD-2)
    def __truediv__(a,b):
        return a*a.cv(b).inv()
    def __rtruediv__(a,b):
        return a.cv(b)*a.inv()
    def __bool__(a): return any(a.c)
    def __eq__(a,b):return a.c==a.cv(b).c
    def __hash__(a):return hash(a.c)
    def __repr__(a):return str(a.c)
    def pair(a):
        assert not any(a.c[1:]),a
        return dec(a.c[0])

t=K([0,1,0,0,0,0,0,0])
rho=K.base(0,1)
assert rho*rho==2 and t**8==2+rho
# Polynomial divides X^(5^16)-X and t^(5^8)=-t,
# with t nonzero in every quotient factor. Therefore irreducible.
assert t**(5**8)==-t and t**MOD==t
assert t**((MOD-1)//2)==-1
om=(-1+rho)/2
assert om**2+om+1==0

def sqrt(a):
    if not a:return a
    assert a**((MOD-1)//2)==1
    m=MOD-1
    s=0
    while m%2==0: m//=2; s+=1
    c=t**m
    x=a**((m+1)//2)
    z=a**m
    while z!=1:
        j=0
        b=z
        while b!=1:
            b=b*b
            j+=1
        assert 0<j<s
        y=c**(1<<(s-j-1))
        x=x*y
        z=z*y*y
        c=y*y
        s=j
    assert x*x==a
    return x

def add(P,Q,B=K(1)):
    if P is None:return Q
    if Q is None:return P
    x,y=P
    u,v=Q
    if x==u:
        if y+v==0:return None
        h=3*x*x/(2*y)
    else:
        h=(v-y)/(u-x)
    X=h*h-x-u
    R=(X,h*(x-X)-y)
    assert R[1]**2==R[0]**3+B
    return R

def neg(P):
    return None if P is None else (P[0],-P[1])

def smul(n,P,B=K(1)):
    z=None
    while n:
        if n%2:z=add(z,P,B)
        n//=2
        if n:P=add(P,P,B)
    return z

def spans(P,Q,m):
    ps=[None]
    qs=[None]
    for i in range(m-1):
        ps.append(add(ps[-1],P))
        qs.append(add(qs[-1],Q))
    assert add(ps[-1],P) is None and add(qs[-1],Q) is None
    return ps,qs

def omega(P):
    return None if P is None else (om*P[0],P[1])

def frob(P):
    return None if P is None else (P[0]**5,P[1]**5)

def half(P):
    x,y=P
    r=[sqrt(x+c) for c in (K(1),om,om**2)]
    if r[0]*r[1]*r[2]!=-y:r[0]=-r[0]
    assert r[0]*r[1]*r[2]==-y
    b=r[0]*r[1]+r[1]*r[2]+r[2]*r[0]
    Q=(x+b,-y-sum(r,K())*b)
    assert Q[1]**2==Q[0]**3+1 and add(Q,Q)==P
    return Q

T=(K(-1),K())
for j in range(4):T=half(T)
U=omega(T)
assert smul(16,T)==(K(-1),K()) and smul(16,U)==(-om,K())
assert smul(32,T) is None
ts,us=spans(T,U,32)
td={P:i for i,P in enumerate(ts)}
assert len(td)==32

def coords32(P):
    matches=[]
    for j,Q in enumerate(us):
        R=add(P,neg(Q))
        if R in td:matches.append((td[R],j))
    assert len(matches)==1,matches
    return matches[0]

def matrix(f,P,Q,coord):
    a,b=coord(f(P));c,d=coord(f(Q))
    return (a,c,b,d)

def madd(x,y,m):
    return tuple((a+b)%m for a,b in zip(x,y))

def mscale(n,g,m):
    return tuple(n*a%m for a in g)

def mmul(x,y,m):
    return tuple(sum(x[i*2+k]*y[k*2+j] for k in range(2))%m
                 for i,j in product(range(2),repeat=2))

def mv(x,P,m):
    return ((x[0]*P[0]+x[1]*P[1])%m,(x[2]*P[0]+x[3]*P[1])%m)

def det(g):
    return g[0]*g[3]-g[1]*g[2]

def mi(g,m):
    s=pow(det(g)%m,-1,m)
    return tuple(s*a%m for a in (g[3],-g[1],-g[2],g[0]))

I=(1,0,0,1)
O2=matrix(omega,T,U,coords32)
F2=matrix(frob,T,U,coords32)
J2=madd(I,mscale(2,O2,32),32)
G2=mmul(madd(F2,mscale(-1,I,32),32),mi(J2,32),32)
assert mmul(F2,F2,32)==mscale(-5,I,32)
assert O2==(0,31,1,31)
assert mmul(G2,J2,32)==madd(F2,mscale(-1,I,32),32)
rho_tan=1+2*om
velu_s=-1/rho_tan
assert velu_s**6==2

def two(P,k):
    if P is None:return None
    x,y=P
    if x==k:return None
    b=3*k*k
    return x+b/(x-k), y*(1-b/(x-k)**2)

def gamma(P):
    Q=two(P,K(-1))
    if Q is None:return None
    X,Y=Q
    return (X/(velu_s*velu_s),Y/(velu_s**3))

# Test the exact arithmetic of gamma used also at the prime dividing its
# denominator in the quaternion basis.  Both actual torsion bases checked.
assert matrix(gamma,T,U,coords32)==G2
S,Q=(K(0),K(1)),(K(1),rho)
assert smul(3,S) is None and smul(3,Q) is None
ss,qs=spans(S,Q,3)
point3={add(P,R):(i,j) for i,P in enumerate(ss) for j,R in enumerate(qs)}
assert len(point3)==9
O3=matrix(omega,S,Q,point3.__getitem__)
G3=matrix(gamma,S,Q,point3.__getitem__)
F3=matrix(frob,S,Q,point3.__getitem__)
assert mmul(G3,madd(I,mscale(2,O3,3),3),3)==madd(F3,mscale(-1,I,3),3)
basis2=[I,O2,G2,mmul(O2,G2,32)]
basis3=[I,O3,G3,mmul(O3,G3,3)]

lines=[(1,i) for i in range(32)]+[(i,1) for i in range(0,32,2)]
def chain(i,j):
    P=add(ts[i],us[j])
    B,torsion=K(1),[]
    for m in [16,8,4,2,1]:
        R=smul(m,P,B)
        assert R is not None and R[1]==0
        x=R[0]
        torsion.append(x.pair())
        P=two(P,x)
        B-=7*x*(3*x*x)
    assert P is None
    return tuple(torsion)

literal_mark={tuple(map(tuple,row['first_kernel_chain'])):row
              for row in src['basis_vertices']}
assert len(literal_mark)==16
chosen={}
full={C:chain(*C) for C in lines}
assert len(set(full.values()))==48
for C,rr in full.items():
    if rr in literal_mark:
        row=literal_mark[rr]
        assert row['i'] not in chosen
        chosen[row['i']] = (C,K.base(*row['actual_normalized_f_32']))
assert len(chosen)==16
line_rows=[[i,*C] for i,(C,f) in sorted(chosen.items())]

def normalized_line(C):
    a,b=C
    if a%2:return (1,b*pow(a,-1,32)%32)
    assert b%2
    return (a*pow(b,-1,32)%32,1)


canon={C:i for i,(C,_) in chosen.items()}
def frob_mark(C):
    D=mv(F2,C,32)
    for j in range(3):
        X=normalized_line(D)
        if X in canon:return (canon[X],j)
        D=mv(O2,D,32)
    raise AssertionError(C)


def eis_times_omega(u,k):
    a,b=u
    for _ in range(k%3):
        a,b=-b,a-b
    return (a,b)


def source_vector(u1,u2,u3):
    return (u1+u3,2*u1,2*u2,2*u3)


def frob_key(record):
    _,a,b,c=record['v']
    u1,u2,u3=a//2,b//2,c//2
    i,j=frob_mark(chosen[record['label']][0])
    # Frob conjugates A and B in A+B F.  A is trace-zero.
    # Changing the target to the canonical mark conjugates by omega^j.
    u2p,u3p=eis_times_omega((-u2+u3,u3),2*j)
    three_u1p=-(3*u1+2*u2-u3)-2*u2p+u3p
    assert three_u1p%3==0
    return (i,source_vector(three_u1p//3,u2p,u3p))


def class_number(D):
    # Independent characteristic-zero check: enumerate primitive reduced
    # binary forms and do not count the two copies on a boundary.
    n=0
    for a in range(1,isqrt((-D)//3)+1):
        for b in range(-a,a+1):
            m=b*b-D
            if m%(4*a):continue
            c=m//(4*a)
            if a>c:continue
            if (abs(b)==a or a==c) and b<0:continue
            if gcd(gcd(a,abs(b)),c)!=1:continue
            n+=1
    return n


def evaluate(v,bs,m):
    g=(0,0,0,0)
    for c,b in zip(v,bs):
        g=madd(g,mscale(c,b,m),m)
    return g

def n3(v):
    return next(c if c==1 else -1
                for a,b in [(1,0),(0,1),(1,1),(1,2)] if
                (c:=(a*mv(v,(a,b),3)[1]-b*mv(v,(a,b),3)[0])%3)!=0)

def vectors(q):
    lim=isqrt(3*q)
    for u2 in range(-lim,lim+1):
        for u3 in range(-lim,lim+1):
            n=u2*u2-u2*u3+u3*u3
            R=45*q-20*n
            if R<0:continue
            t=isqrt(R)
            if t*t!=R:continue
            for w in ((-t,t) if t else (0,)):
                z=w-2*u2+u3
                if z%3:continue
                u1=z//3
                yield (u1,u2,u3)

def scalar(a):
    r=a.pair()
    assert r[1]==0
    return r[0]

def leg(a,p):
    z=pow(a%p,(p-1)//2,p)
    return 0 if not z else (1 if z==1 else -1)

def one_q(q):
    assert q==1 or (q%8==1 and all(q%d for d in range(2,isqrt(q)+1)))
    delta=-15*q
    m=(1-delta)//4
    roots=[a for a in range(32) if (a*a-a+m)%32==0]
    assert len(roots)==2 and sum(x%2 for x in roots)==1,roots
    vf=list(vectors(q))
    assert len(set(vf))==len(vf)
    ans={'q':q,'delta':delta,'gross_vectors_on_one_bare_curve':len(vf),'h_reduced_forms':class_number(delta),'orientations':[]}
    for root in sorted(roots):
        terms=[]
        unweighted=K()
        weighted=K()
        for u1,u2,u3 in vf:
            # v=2u-tr(u); Omega=(1+v)/2 integral.
            tr=-u1-u3
            assert tr%2
            v=source_vector(u1,u2,u3)
            Omega=((1-tr)//2,u1,u2,u3)
            w=evaluate(v,basis3,3)
            assert any(w) and mmul(w,w,3)==(0,0,0,0)
            e=n3(w)
            c=2*rho_tan*(u2+u3*om)/3
            assert c and c**(5+1)==(-delta//5)%5
            mat=evaluate(Omega,basis2,32)
            for i,(C,f) in sorted(chosen.items()):
                if mv(mat,C,32)!=tuple(root*z%32 for z in C):continue
                # Hasse = 2A, KS(omega²)=dA/6. F=f_32/(12).
                d=f/12*c
                weighted+=e*d
                unweighted+=d
                terms.append(dict(label=i,v=v,nilpotent=w,e=e,c=c.pair(),
                                  F=(f/12).pair(),raw_normalized_term=d.pair()))
        # No sign is picked per term. Use one base e for each orbit.
        # For Δ=-15 odd branch ensure the same base CM label as the donor.
        if q==1 and root%2:
            base=next(row for row in terms if row['label']==3)
        else:
            base=terms[0] if terms else None
        assert base is not None
        assert weighted**5==-weighted and unweighted**5==unweighted
        # Actual primitive based isogeny has u_p=-2 relative to normalized f32.
        j=4*(-2)*rho/(delta//5)*base['e']*weighted
        abs_j=scalar(j)
        assert len(terms)==ans['h_reduced_forms']
        keyed={(z['label'],z['v']):z for z in terms}
        assert len(keyed)==len(terms)
        seen=set()
        nonzero_pairs=0
        sample_pair=None
        for key,z in sorted(keyed.items()):
            if key in seen: continue
            fk=frob_key(z)
            assert fk!=key
            other=keyed[fk]
            assert frob_key(other)==key
            assert other['e']==-z['e']
            left=K.base(*z['raw_normalized_term'])
            right=K.base(*other['raw_normalized_term'])
            assert right==left**5
            pair=z['e']*left + other['e']*right
            assert pair**5==-pair
            if pair:
                nonzero_pairs+=1
                if sample_pair is None:
                    sample_pair=dict(keys=[key,fk],raw_signed_pair=pair.pair())
            seen|={key,fk}
        assert len(seen)==len(terms)
        ans['orientations'].append(dict(root_on_C32=root,n_terms=len(terms),
                              signed_raw=weighted.pair(),unweighted_control=unweighted.pair(),
                              base=[base['label'],base['v'],base['e']],
                              based_jet_mod5=abs_j,nonzero_signed_Frob_pairs=nonzero_pairs,
                              sample_pair=sample_pair,terms=terms))
    assert ans['orientations'][0]['signed_raw']==ans['orientations'][1]['signed_raw']
    if q==1:
        same=next(o for o in ans['orientations'] if o['root_on_C32']%2)
        assert sorted(t['label'] for t in same['terms'])==[1,3]
        assert same['based_jet_mod5']==src['actual_J5'][0],same
    if q==89:
        assert all(o['unweighted_control']==(0,0) and o['based_jet_mod5']
                   for o in ans['orientations'])
    if q in (257,2113,3881):
        assert all(o['nonzero_signed_Frob_pairs'] and not o['based_jet_mod5']
                   for o in ans['orientations'])
    return ans

ans=[one_q(q) for q in args.q]
print(json.dumps({'literal_labels_sha256':sha256(raw).hexdigest(), 'F5_16_chart':'t^8=2+rho; rho²=2',
                  'omega_and_gamma_mod32':[O2,G2], 'omega_and_gamma_mod3':[O3,G3],
                  'line_frames':line_rows, 'q_shells':ans},indent=2))
