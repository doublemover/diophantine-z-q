#!/usr/bin/env python3
"""Actual squarefree N=33 ramified CM35 and sparse anchored mod-5 jet certificate."""
from itertools import product
import json

class K:
    """F25[ε]/(ε²), ρ²=2, ordered 1,ρ,ε,ερ."""
    def __init__(self,*v): self.v=tuple(int(x)%5 for x in v)+(0,)*(4-len(v))
    @staticmethod
    def c(x):
        assert isinstance(x,(int,K)),x
        return x if isinstance(x,K) else K(x)
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

# F25 polynomials, exact arithmetic; tuples have low-to-high coefficients.
def tr(p):
    p=list(map(K.c,p))
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p or [K(0)])
P0=tr([0]); P1=tr([1]); T=tr([0,1])
def pa(p,q):
    z=[K(0)]*max(len(p),len(q))
    for coeffs in (p,q):
        for i,a in enumerate(coeffs):z[i]+=a
    return tr(z)
def ps(p,s):return tr([K.c(s)*a for a in p])
def pm(p,q):
    z=[K(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):z[i+j]+=a*b
    return tr(z)
def pd(p,q):
    assert q!=P0
    r=p; z=[K(0)]*max(1,len(p)-len(q)+1)
    while len(r)>=len(q) and r!=P0:
        m=len(r)-len(q); c=r[-1]/q[-1]; z[m]+=c
        r=pa(r,tr([0]*m+list(ps(q,-c))))
    return tr(z),r
def rm(p,q):return pd(p,q)[1]
def pp(p,n):
    if n==0:return P1
    t=pp(p,n//2)
    return pm(pm(t,t),p if n%2 else P1)
def deriv(p):return tr([i*p[i] for i in range(1,len(p))])
def mon(p):return ps(p,1/p[-1])
def gc(p,q):
    while q!=P0:p,q=q,rm(p,q)
    return mon(p)
def invmod(p,m):
    a,b=m,rm(p,m); t,u=P0,P1
    while b!=P0:
        q,r=pd(a,b); a,b=b,r;t,u=u,pa(t,ps(pm(q,u),-1))
    assert len(a)==1 and a!=P0
    return rm(ps(t,1/a[0]),m)
def rat(a,b): # no need to keep denominator monic
    g=gc(a,b); a,r=pd(a,g); b,s=pd(b,g)
    assert r==P0 and s==P0
    return a,b
def ra(f,g):return rat(pa(pm(f[0],g[1]),pm(g[0],f[1])),pm(f[1],g[1]))
def rs(f,a):return ps(f[0],a),f[1]
def ri(f):return f[1],f[0]
def r2(A,B,r):
    b=3*r*r+A
    return ra((T,P1),(tr([b]),tr([-r,1])))
def r3(A,B,r,X=(T,P1)):
    u=ri(ra(X,(tr([-r]),P1)))
    b=2*(3*r*r+A)
    d=4*(r**3+A*r+B)
    return ra(X,ra(rs(u,b),rat(ps(pm(u[0],u[0]),d),pm(u[1],u[1]))))
def e_poly(e,p):
    z=K(0)
    for a in p[::-1]:z=z*e+a
    return z
def ev(e,f):return e_poly(e,f[0])/e_poly(e,f[1])
def encoded(p):return tuple(a.pair() for a in p)

def RREF(rows,n):
    R=[row[:] for row in rows]; piv=[]
    for j in range(n):
        k=next((i for i in range(len(piv),len(R)) if R[i][j]!=0),None)
        if k is None:continue
        i=len(piv); R[i],R[k]=R[k],R[i]; t=R[i][j]
        R[i]=[x/t for x in R[i]]
        for k in range(len(R)):
            if k!=i and R[k][j]!=0:
                t=R[k][j];R[k]=[x-t*y for x,y in zip(R[k],R[i])]
        piv.append(j)
    return R,piv
def image(P,f):
    f0,f1=f
    v=rm(pm(rm(f0,P),invmod(f1,P)),P)
    rows=[P1]
    for _ in range(len(P)-1):rows.append(rm(pm(rows[-1],v),P))
    m=len(P)-1
    R,piv=RREF([[(Q[j] if len(Q)>j else K(0)) for Q in rows] for j in range(m)],m)
    assert len(piv)==m
    Q=tr([-u[-1] for u in R]+[1])
    assert gc(Q,deriv(Q))==P1
    return Q

def put2(Ps,Q):
    if Q is None:return (0,0)
    if Q==Ps[0]:return (1,0)
    if Q==Ps[1]:return (0,1)
    assert Q==group_add(K(0),*Ps)
    return (1,1)

# Norm-nine actual CM endomorphism, horizontal 3², with differential 1/2.
A0,B0=K(0),K(1)
Ps=[(r,K(0)) for r in roots(A0,B0)][:2]
s=K(3)
choices=[]
for R in full3(A0,B0):
    A1,B1=quot3(A0,B0,R)
    other=next(Q for Q in full3(A0,B0) if Q[0]!=R[0])
    dual=three_image(A0,B0,R,other)
    for S in full3(A1,B1):
        if S[0]==dual[0]:continue
        A2,B2=quot3(A1,B1,S)
        assert (A2,B2)==(A0,B0*s**6)
        imgs=[]
        for P in Ps:
            X,Y=three_image(A1,B1,S,three_image(A0,B0,R,P))
            imgs.append((X/s**2,Y/s**3))
        mat=[put2(Ps,Q) for Q in imgs]
        if (mat[0][0]+mat[1][1])%2!=1:continue
        choices.append((R,S,mat))
assert len(choices)==6
R,S,mat=choices[0]
A1,B1=quot3(A0,B0,R)
f1=r3(A0,B0,R[0]); f2=r3(A1,B1,S[0])
gam=rs(r3(A1,B1,S[0],f1),1/s**2)
a,b=gam
ker11=gc(pa(a,ps(pm(T,b),-1)),pa(pa(pm(deriv(a),b),ps(pm(a,deriv(b)),-1)),ps(pm(b,b),s)))
assert len(ker11)==6
assert gc(ker11,deriv(ker11))==P1
assert gc(ker11,b)==P1
assert encoded(ker11)==((0,4),(2,3),(1,0),(3,0),(4,2),(1,0))
k2=image(ker11,f1)
# Rational equivariance with actual CM. Two distinct level labels should remain.
def normalize(B,r,P):
    options=[]
    for s in FF:
        if s**6!=B:continue
        cand=(r/s**2,tr([a*s**(2*i-2*(len(P)-1)) for i,a in enumerate(P)]))
        options.append((cand,s))
    key=lambda it:(it[0][0].pair(),encoded(it[0][1]),it[1].pair())
    return min(options,key=key)
v1,w1=normalize(B0,R[0],ker11); v2,w2=normalize(B1,S[0],k2)
assert v1!=v2
# α=2γ−1, normalized degree-three x-Vélu t=2·(3r²+A).
# Composition derivative is s, [2] ->1, so first coefficient is 2(t1+t2).
c=2*(2*(3*R[0]**2+A0)+2*(3*S[0]**2+A1))
assert c!=0 and c**6==2 # [5] leads with −z^25, so alpha²=[−35] predicts c*c^5=7.
rt=2*z # rho²=−7=3
c1=c*w1**(1-5); c2=c*w2**(1-5)
Lpair=[c1*rt/(-7)/2/6, -c2*rt/(-7)/2/6]
assert c==K(3,1) and Lpair==[K(4,1),K(4,4)]
def t2(ar):
    R,P=ar; out=[]
    for r in roots(A0,B0):
        _,B1=red2(A0,B0,r); g=r2(A0,B0,r)
        RR=ev(R,g); PP=image(P,g)
        vv,scale=normalize(B1,RR,PP)
        out.append((vv,scale**2/2))
    assert len(out)==3
    return out
adj={}; pending=[v1,v2]
while pending:
    v=pending.pop()
    if v in adj:continue
    adj[v]=t2(v)
    pending.extend(w for w,_ in adj[v] if w not in adj)
labs=sorted(adj)
assert len(labs)==16
i,j=labs.index(v1),labs.index(v2)
n=len(labs)
def zero():return [K(0)]*n
T2=[]
# a2=1 from affine count1 at 2 on 33a1 y²+xy=x³+x²−11x.
assert 1+sum((y*y+x*y-x*x*x-x*x+11*x)%2==0 for x,y in product(range(2),repeat=2))==2
for v in labs:
    row=zero()
    for q,w in adj[v]:row[labs.index(q)]+=w
    row[labs.index(v)]-=1
    T2.append(row)
L=zero();L[i],L[j]=Lpair
# The opposite 11-kernel is (2−gamma)P=0.
dbl=rat(tr([0,-8,0,0,1]),tr([4,0,0,4]))
def rd(f):
    a,b=f
    return rat(pa(pm(deriv(a),b),ps(pm(a,deriv(b)),-1)),pm(b,b))
def rm_quot(f,c):return rs(rd(f),1/K.c(c))
def rnsub(f,g):
    return ra(f,rs(g,-1))[0]
bar11=gc(rnsub(gam,dbl),rnsub(rm_quot(gam,s),rm_quot(dbl,2)))
bar11,_=pd(bar11,gc(bar11,tr([1,0,0,1])))
assert len(bar11)==6 and gc(bar11,ker11)==P1
# W11 preserves the C3 line in the actual endomorphism gamma+1.
def w3(v):
    r,P=v
    Q=next(Q for Q in full3(A0,B0) if Q[0]==r)
    Tq=next(Tq for Tq in full3(A0,B0) if Tq[0]!=r)
    dual=three_image(A0,B0,Q,Tq)[0]
    _, B1=quot3(A0,B0,Q)
    return normalize(B1,dual,image(P,r3(A0,B0,r)))[0]
def frob(v):
    r,P=v
    vv,u=normalize(B0,r**5,tr([c**5 for c in P]))
    return vv
v1b=normalize(B0,R[0],bar11)[0]
v2b=normalize(B1,S[0],image(bar11,f1))[0]
orb={v1,v1b,w3(v1),w3(v1b)}
big=orb|{frob(v) for v in orb}
assert sorted(labs.index(v) for v in big)==[5,7,12,14]

# Weighted Atkin arrows on arbitrary exact roster rows.
def ratmul(f,g):return rat(pm(f[0],g[0]),pm(f[1],g[1]))
def velu11(P):
    G=rat(deriv(P),P)
    G2=ra(ratmul(G,G),rs(rat(deriv(deriv(P)),P),-1))
    t=-P[-2]; f=tr([1,0,0,1]); d=len(P)-1
    return ra(ra(rs((T,P1),1+2*d),(tr([-2*t]),P1)),
              ra(rs(ratmul((f,P1),G2),4),rs(ratmul((deriv(f),P1),G),-2)))
polys=set()
for r,P in labs:
    for a in FF:
        if a**3==1:
            polys.add(tr([c*a**(i-(len(P)-1)) for i,c in enumerate(P)]))
assert len(polys)==12
polys=sorted(polys,key=encoded)
def w3weight(v):
    r,P=v
    Q=next(Q for Q in full3(A0,B0) if Q[0]==r)
    Tq=next(Tq for Tq in full3(A0,B0) if Tq[0]!=r)
    dual=three_image(A0,B0,Q,Tq)[0]
    _,B1=quot3(A0,B0,Q)
    v,sc=normalize(B1,dual,image(P,r3(A0,B0,r)))
    return v,sc**2/3
def w11weight(v):
    r,P=v; R=velu11(P)
    Pother=next(Q for Q in polys if Q!=P)
    # Every independent cyclic 11 line maps onto the same dual C11.
    Pdual=image(Pother,R)
    v,sc=normalize(B0,ev(r,R),Pdual)
    return v,sc**2/11
assert w11weight(v1)[0]==v1b
WW={}; WD={}
for ww,ap,wp in [(3,-1,w3weight),(11,1,w11weight)]:
    assert ww+1-(1+sum((y*y+x*y-x*x*x-x*x+11*x)%ww==0 for x,y in product(range(ww),repeat=2)))==ap
    rows=[]; inds=[]
    for q in labs:
        dest,co=wp(q); row=zero(); row[labs.index(dest)]+=co; row[labs.index(q)]+=ap
        rows.append(row); inds.append(labs.index(dest))
    WW[ww]=rows; WD[ww]=inds

# Actual W3, W11 and residue Frobenius force e0 to be a nonzero anchor
# for any nonzero simultaneous AL eigen-differential of this genus-three curve.
Frob=[labs.index(frob(q)) for q in labs]
seen={0}; todo=[0]
while todo:
    j=todo.pop()
    for k in (WD[3][j],WD[11][j],Frob[j]):
        if k not in seen:
            seen.add(k);todo.append(k)
orbit=sorted(seen)
assert orbit==[0,1,2,3,8,9,10,11]
assert len(orbit)>2*3-2

# Direct sparse coefficient check, not an eigenline calculation.
assert (labs.index(v1),labs.index(v2))==(7,5)
Ts=[(0,K(0,3)),(5,K(4,4)),(9,K(2,2)),(15,K(3,1))]
Ws=[(3,0,K(3,2)),(3,7,K(1,1)),(3,8,K(1,3)),(11,2,K(4,4))]
for q,x in enumerate(L):
    y=(z if q==0 else K(0))
    y+=sum((u*T2[j][q] for j,u in Ts),K(0))
    y+=sum((u*WW[w][j][q] for w,j,u in Ws),K(0))
    assert x==y
touched={0}
touched.update(j for j,x in enumerate(L) if x!=0)
for j,_ in Ts:touched.update(k for k,x in enumerate(T2[j]) if x!=0)
for w,j,_ in Ws:touched.update(k for k,x in enumerate(WW[w][j]) if x!=0)
assert sorted(touched)==[0,1,2,5,7,8,9,12,15]
assert 2+2*7-(1+sum((y*y+x*y-x*x*x-x*x+11*x)%7==0 for x,y in product(range(7),repeat=2)))==12

def sparse(row):
    return [[j,c.pair()] for j,c in enumerate(row) if c!=0]
print(json.dumps(dict(
    curve='X0(33) good at 5, new form attached to y²+xy=x³+x²−11x',
    residue_field='F5[z]/(z²−2)', CM_bridge=dict(norm9_kernels=[R[0].pair(),S[0].pair()],
           action_matrix_on_E2_columns=mat, derivative=s.pair(),
           directed_kernel11=encoded(ker11), opposite_kernel11=encoded(bar11),
           oriented_alpha_first_coefficient=c.pair(), local_sqrt_minus7=rt.pair(),
           exact_CM_indices=[labs.index(v1),labs.index(v2)], scales=[w1.pair(),w2.pair()]),
    all_vertices=[dict(i=j, kernel3=r.pair(), kernel11=encoded(P)) for j,(r,P) in enumerate(labs)],
    jet_row=sparse(L), anchor=dict(i=0,scalar=z.pair(),Atkin_and_Frob_orbit=orbit,
        arrows=[[j,WD[3][j],WD[11][j],Frob[j]] for j in orbit]),
    T2_minus_1_rows=[dict(source=j,multiplier=u.pair(),coefficients=sparse(T2[j])) for j,u in Ts],
    Atkin_minus_eigen_rows=[dict(level=w,source=j,multiplier=u.pair(),coefficients=sparse(WW[w][j])) for w,j,u in Ws],
    all_touched_vertices=sorted(touched)),indent=2))
