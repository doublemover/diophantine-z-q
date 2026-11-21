#!/usr/bin/env python3
"""W32 and exact sparse weighted T3 certificate on actual X0(32)/F5."""
from itertools import product
import json

class K:
    """F25[ε]/(ε²), ρ²=2, ordered 1,ρ,ε,ερ."""
    def __init__(self,*v): self.v=tuple(int(x)%5 for x in v)+(0,)*(4-len(v))
    @staticmethod
    def c(x): return x if isinstance(x,K) else K(x)
    def __add__(a,b): return K(*(x+y for x,y in zip(a.v,a.c(b).v)))
    __radd__=__add__
    def __neg__(a): return K(*(-x for x in a.v))
    def __sub__(a,b): return a+-a.c(b)
    def __rsub__(a,b): return a.c(b)+-a
    def __mul__(a,b):
        bv=a.c(b).v; z=[0]*4
        for i,j in product(range(4),repeat=2):
            if i&j&2:continue
            z[i^j]+=a.v[i]*bv[j]*(2 if i&j&1 else 1)
        return K(*z)
    __rmul__=__mul__
    def __pow__(a,n):
        if n<0:return a.inv()**(-n)
        if not n:return K(1)
        h=a**(n//2)
        return h*h*(a if n%2 else 1)
    def res(a):return K(*a.v[:2])
    def lin(a):return K(*a.v[2:])
    def inv(a):
        x,y=a.v[:2]; n=(x*x-2*y*y)%5
        assert n,a.v
        t=K(x,-y)*pow(n,-1,5)
        return t*(2-a*t)
    def __truediv__(a,b):return a*a.c(b).inv()
    def __rtruediv__(a,b):return a.c(b)*a.inv()
    def __eq__(a,b):return a.v==a.c(b).v
    def __lt__(a,b):return a.v<b.v
    def __hash__(a):return hash(a.v)
    def __repr__(a):return str(a.v[:2] if not (a.v[2] or a.v[3]) else a.v)
    def pair(a): assert a==a.res(); return a.v[:2]

e=K(0,0,1)
z=K(0,1)
FF=[K(a,b) for a,b in product(range(5),repeat=2)]
def roots(A,B):
    for x in FF:
        f=x**3+A*x+B
        if f.res()==0:
            d=(3*x*x+A).res()
            assert d!=0
            yield x-e*f.lin()/d

def red2(A,B,x):
    assert x**3+A*x+B==0
    b=3*x*x+A
    return (A-5*b,B-7*x*b)

def two_image(A,B,r,P):
    if P is None:return None
    x,y=P
    if x==r:return None
    b=3*r*r+A
    return x+b/(x-r),y*(1-b/(x-r)**2)

def chains(A,B,n,prev=None):
    if not n:
        yield ()
        return
    for r in roots(A,B):
        if prev is not None and r==prev:continue
        a,b=red2(A,B,r)
        for tail in chains(a,b,n-1,-2*r):
            yield (r,*tail)

def t8(rr):
    r,t,s=rr
    v,vp=(t-r)/2,(s-t)/2
    return 32*v/(vp-4*v)

def t16(rr):
    A,B=t8(rr[:3]),t8(rr[1:])
    X=(B-2*A)/(A+4)
    assert X*X==(X+2)*A and X*(X+4)==B
    return X

def coords(rr):
    U,V=t16(rr[:4]),t16(rr[1:])
    X=2+V
    # w32(P)=(2,4)-P; T16(z)*T16(2*w32(z))=8.
    Y=((X-2)**2*(4+X+8/U)-X**3-4*X-16)/8
    assert Y*Y==X**3+4*X
    return X,Y

# Enumerate all 48 nonbacktracking chains and all actual 16 modular labels.
records={}
for rr in chains(e,K(1),5):
    X,Y=coords(rr)
    P=(X.res(),Y.res())
    assert Y.res()!=0
    # KS(ω²) = dA/6 at A=0,B=1. Tian ordinate has +q^-3, so f=-dX/(2Y).
    f=-6*X.lin()/(2*Y.res())
    r=tuple(x.res() for x in rr)
    if P in records:
        u2=r[0]/records[P][0][0]
        assert u2**3==1
        assert tuple(x/u2 for x in r)==records[P][0]
        assert f==u2*records[P][1]
        records[P][2].append(r)
    else:
        records[P]=[r,f,[r]]
assert len(records)==16 and {len(R[2]) for R in records.values()}=={3}
labels=sorted(records)
basis=[records[P][1] for P in labels]
assert all(f!=0 for f in basis)
rev={vv:k for k,(P,R) in enumerate((P,records[P]) for P in labels) for vv in R[2]}

def group_add(A,P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P; X,Y=Q
    if x==X and y+Y==0:return None
    m=(3*x*x+A)/(2*y) if x==X else (Y-y)/(X-x)
    X0=m*m-x-X
    return X0,m*(x-X0)-y

def three_image(A,B,Q,P):
    if P is None:return P
    RR=[Q,(Q[0],-Q[1])]
    XX,YY=P
    for S in RR:
        Z=group_add(A,P,S)
        assert Z is not None
        XX+=Z[0]-S[0]; YY+=Z[1]-S[1]
    return XX,YY

def quot3(A,B,Q):
    x=Q[0]
    return A-10*(3*x*x+A),B-14*(5*x**3+3*A*x+2*B)

def full3(A,B):
    for x in FF:
        if 3*x**4+6*A*x*x+12*B*x-A*A!=0:continue
        for y in FF:
            if y*y==x**3+A*x+B and y!=0:
                P=(x,y)
                P2=group_add(A,P,P)
                assert group_add(A,P2,P) is None
                yield P; break

def three_hecke(rr):
    Bs=K(1)
    us=[]
    for Q in full3(K(0),Bs):
        A0,B0=K(0),K(1)
        At,Bt=quot3(A0,B0,Q)
        assert At==0
        s=next(s for s in FF if s**6==Bt)
        rr2=[]
        for r in rr:
            x,y=three_image(A0,B0,Q,(r,K(0)))
            assert y==0
            rr2.append(x/(s*s))
            A1,B1=red2(A0,B0,r)
            At1,Bt1=red2(At,Bt,x)
            Q=two_image(A0,B0,r,Q)
            assert Q is not None
            assert quot3(A1,B1,Q)==(At1,Bt1)
            A0,B0,At,Bt=A1,B1,At1,Bt1
        j=rev[tuple(rr2)]
        u2=rr2[0]/records[labels[j]][0][0]
        assert tuple(x/u2 for x in rr2)==records[labels[j]][0]
        us.append((j,s*s*u2/3))
    assert len(us)==4
    return us

def atkin32(rr):
    A,B=K(0),K(1)
    for r in rr:A,B=red2(A,B,r)
    s=next(s for s in FF if s**6==B)
    dest=tuple(-2*r*pow(4,i,5)/(s*s) for i,r in enumerate(rr[::-1]))
    j=rev[dest]
    u2=dest[0]/records[labels[j]][0][0]
    assert tuple(x/u2 for x in dest)==records[labels[j]][0]
    return j,s*s*u2/32

def dot(row,v):return sum((a*b for a,b in zip(row,v)),K(0))
rows3=[]; rowsW=[]
zeros=lambda:[K(0) for _ in labels]
for i,k in enumerate(labels):
    rr=records[k][0]; R=zeros(); S=zeros()
    for j,c in three_hecke(rr):R[j]+=c
    j,c=atkin32(rr); S[j]+=c
    assert labels[j]==group_add(K(4),(K(2),K(4)),(k[0],-k[1]))
    S[i]+=1
    assert dot(R,basis)==0 and dot(S,basis)==0
    for a in records[k][2]:
        R0=zeros()
        for j,c in three_hecke(a):R0[j]+=c
        u2=a[0]/rr[0]
        assert R0==[u2*x for x in R]
        j1,c1=atkin32(a)
        j0,c0=atkin32(rr)
        assert (j1,c1)==(j0,u2*c0)
    rows3.append(R);rowsW.append(S)
def rref(rows):
    Y=[row[:] for row in rows]; piv=[]
    for j in range(len(labels)):
        k=next((k for k in range(len(piv),len(Y)) if Y[k][j]!=0),None)
        if k is None: continue
        d=len(piv); Y[k],Y[d]=Y[d],Y[k]
        u=Y[d][j]; Y[d]=[x/u for x in Y[d]]
        for i in range(len(Y)):
            if i!=d and Y[i][j]!=0:
                u=Y[i][j];Y[i]=[x-u*y for x,y in zip(Y[i],Y[d])]
        piv.append(j)
    return Y,piv
def kernel(rows):
    Y,piv=rref(rows); out=[]
    for j in range(len(labels)):
        if j in piv:continue
        q=zeros();q[j]=K(1)
        for i,k in enumerate(piv):q[k]=-Y[i][j]
        out.append(q)
    return out

P1=((K(-1)-3*z)/4,K(1)/2)
P2=((K(-1)+3*z)/4,K(1)/2)
i,j=map(labels.index,(P1,P2))
cm_indices=(i,j)
assert cm_indices==(3,1)
# The actual +Y orientation of the CM15 source, same ε normalization.
omega1=(1-z)/4; omega2=(-1-z)/4
A1=(1-z)*records[P1][0][0]**2; A2=(-1-z)*records[P2][0][0]**2 # conjugation sends ε->-ε and ρ->-ρ
assert -basis[i]*A1/6==omega1 and -basis[j]*A2/6==omega2
L=zeros(); L[i]=-8*A1/6; L[j]=8*A2/6
assert dot(L,basis)==4
K3=kernel(rows3); KW=kernel(rowsW); KC=kernel(rows3+rowsW)
assert (len(K3),len(KW),len(KC))==(1,10,1)
assert dot(L,KC[0])!=0
assert 1+sum((y*y-x**3+x)%3==0 for x,y in product(range(3),repeat=2))==4
RT=[list(v) for v in zip(*rows3)]
KL=kernel(RT)
assert len(KL)==1
best=None
for k,P in enumerate(labels):
    c=4/basis[k]
    rhs=L[:];rhs[k]-=c
    TT,inds=rref([r+[b] for r,b in zip(RT,rhs)])
    assert len(inds)==15 and TT[-1][-1]==0
    sol=zeros()
    for i,j in enumerate(inds): sol[j]=TT[i][-1]
    for a in FF:
        co=[x+a*y for x,y in zip(sol,KL[0])]
        ix=[i for i,x in enumerate(co) if x!=0]
        supports={j for i in ix for j,x in enumerate(rows3[i]) if x!=0}
        supports.update(j for j,x in enumerate(L) if x!=0)
        supports.add(k)
        assert [sum((co[i]*row[j] for i,row in enumerate(rows3)),K(0)) for j in range(len(labels))]==rhs
        key=(len(ix),len(supports),k,tuple(x.pair() for x in co))
        if best is None or key<best[0]:best=(key,co,c,sorted(supports))
assert best[0][:3]==(4,8,1)
selected=[(j,c) for j,c in enumerate(best[1]) if c!=0]
assert selected==[(1,K(3,4)),(3,K(2,4)),(9,K(3,1)),(11,K(2,1))]
assert best[2]==K(3,3) and best[-1]==[1,3,5,7,9,11,13,15]
anchor=best[0][2]; scal=best[2]
# Replay the four-row identity straight from the actual coefficient rows.
for j in range(len(labels)):
    assert L[j]==(scal if anchor==j else 0)+sum((coef*rows3[i][j] for i,coef in selected),K(0))

def det(M):
    M=[r[:] for r in M]; d=K(1)
    for j in range(len(M)):
        k=next((k for k in range(j,len(M)) if M[k][j]!=0),None)
        if k is None:return K(0)
        if k!=j:M[j],M[k]=M[k],M[j];d=-d
        s=M[j][j];d*=s
        for i in range(j+1,len(M)):
            u=M[i][j]/s
            if u!=0:M[i]=[a-u*b for a,b in zip(M[i],M[j])]
    return d
D=[(j,det(rows3[:j]+rows3[j+1:]+[L])) for j in range(len(labels))]
assert any(c!=0 for _,c in D)
assert D[0]==(0,K(1))
def sparse(R):
    return [[i,u.pair()] for i,u in enumerate(R) if u!=0]
print(json.dumps(dict(
    field='F25 = F5[rho]/(rho²-2)', raw_chains=sum(len(rec[2]) for rec in records.values()),
    basis_vertices=[dict(i=i, coordinates=[x.pair() for x in P], first_kernel_chain=[x.pair() for x in records[P][0]],
                         actual_normalized_f_32=basis[i].pair(), T3=sparse(rows3[i]), W32_plus_I=sparse(rowsW[i]))
                    for i,P in enumerate(labels)],
    a3=0, T3_rank=15, minor_omit_row=0, determinant_adjoin_L=D[0][1].pair(),
    CM15_cell_indices=cm_indices, jet_row=sparse(L), actual_J5=dot(L,basis).pair(),
    sparse_positive_cert=dict(anchor=anchor, anchor_scalar=scal.pair(), row_multipliers=[[i,u.pair()] for i,u in selected],
                              all_touched_vertices=best[-1])),indent=2))
