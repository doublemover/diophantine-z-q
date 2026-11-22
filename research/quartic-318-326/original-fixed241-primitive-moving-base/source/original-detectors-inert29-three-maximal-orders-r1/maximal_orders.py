#!/usr/bin/env python3
"""The 3 actual supersingular End lattices in one quaternion frame (requires SymPy)."""
from fractions import Fraction as F
from itertools import product
import json
from math import isqrt
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form

p=29
deg=8
q=p**deg
zero=(0,)*deg
one=(1,)+(0,)*(deg-1)
def fe(x):return (x%p,)+(0,)*(deg-1)
def v(x,i):return tuple(x%p if j==i else 0 for j in range(deg))
s=v(1,4)
u=v(1,1)
def fa(a,b):return tuple((x+y)%p for x,y in zip(a,b))
def fn(a):return tuple(-x%p for x in a)
def fs(a,b):return fa(a,fn(b))
def fm(a,b):
    c=[0]*deg
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j>=deg:c[i+j-deg]+=2*x*y
            else:c[i+j]+=x*y
    return tuple(x%p for x in c)
def fscale(a,n):return tuple(x*n%p for x in a)
def fp(a,n):
    y=one
    while n:
        if n%2:y=fm(y,a)
        a=fm(a,a);n//=2
    return y
def fd(a,b):
    assert b!=zero
    return fm(a,fp(b,q-2))
def square(a):return fm(a,a)
def fr(a):return fp(a,p)
def sqrt(a):
    if a==zero:return zero
    assert fp(a,(q-1)//2)==one
    m=q-1;e=0
    while not m%2:m//=2;e+=1
    c=fp(u,m);t=fp(a,m);r=fp(a,(m+1)//2)
    while t!=one:
        i=1;z=square(t)
        while z!=one:i+=1;z=square(z)
        b=fp(c,2**(e-i-1));r=fm(r,b);c=square(b);t=fm(t,c);e=i
    assert square(r)==a
    return r
# E0: y^2=x^3+1.
def Padd(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;z,w=Q
    if x==z:
        if fa(y,w)==zero:return None
        assert y==w
        sl=fd(fscale(square(x),3),fscale(y,2))
    else:sl=fd(fs(y,w),fs(x,z))
    t=fs(square(sl),fa(x,z))
    return t,fs(fm(sl,fs(x,t)),y)

def Pmul(n,P):
    assert n>=0
    R=None
    while n:
        if n%2:R=Padd(R,P)
        P=Padd(P,P);n//=2
    return R
def Pneg(P):return None if P is None else (P[0],fn(P[1]))
def Pfr(P):return None if P is None else (fr(P[0]),fr(P[1]))
# ζ=(-1+10s)/2, since (10s)^2=-3 in F29.
zeta=fscale(fs(fscale(s,10),one),15)
def om(P):return None if P is None else (fm(zeta,P[0]),P[1])
e=[fe(-1),fn(zeta),fn(square(zeta))]
def half(P):
    x,y=P
    a,b,c=(sqrt(fs(x,r)) for r in e)
    if fm(fm(a,b),c)!=fn(y):a=fn(a)
    assert fm(fm(a,b),c)==fn(y)
    k=fa(fa(fm(a,b),fm(b,c)),fm(c,a))
    Q=fa(x,k),fs(fn(y),fm(fa(fa(a,b),c),k))
    assert Padd(Q,Q)==P
    return Q

# Raw quaternion x+y*w+(z+t*w)*pi. Norm exactly below.
def N(v):
    x,y,z,t=map(F,v)
    return x*x-x*y+y*y+29*(z*z-z*t+t*t)
def tr(v):return 2*v[0]-v[1]
RQ=[
    [F(1),F(0),F(0),F(0)],
    [F(0),F(1),F(0),F(0)],
    [F(0),F(0),F(1),F(0)],
    [F(2,3),F(4,3),F(2,3),F(1,3)],
]
def matmul(A,B,m):return [[sum(A[i][k]*B[k][j] for k in (0,1))%m for j in (0,1)] for i in (0,1)]
def msum(As,Cs,m):return [[sum(c*A[i][j] for A,c in zip(As,Cs))%m for j in (0,1)] for i in (0,1)]
def tates():
    assert fp(u,(q-1)//2)==fe(-1)
    assert fp(s,2)==fe(2)
    assert fa(fa(one,zeta),square(zeta))==zero and zeta!=one
    T2=(fe(-1),zero)
    x=fa(fe(-1),fscale(s,4))
    T4=(x,sqrt(fa(fm(square(x),x),one)))
    assert Pmul(2,T4)==T2
    T=half(half(T4));B=om(T)
    assert Pmul(4,T)==T4 and Pmul(8,T)==T2
    lookup={Padd(Pmul(a,T),Pmul(b,B)):(a,b) for a,b in product(range(16),repeat=2)}
    assert len(lookup)==256
    def mk(f):
        cols=[lookup[f(X)] for X in (T,B)]
        return [list(r) for r in zip(*cols)]
    I,W,Pi=mk(lambda x:x),mk(om),mk(Pfr)
    assert I==[[1,0],[0,1]] and W==[[0,15],[1,15]]
    assert matmul(Pi,Pi,16)==[[3,0],[0,3]]
    assert matmul(Pi,W,16)==matmul(matmul(W,W,16),Pi,16)
    # Integral nu = (2+4*w+2*pi+w*pi)/3, 3 unit mod 16.
    nu=msum((I,W,Pi,matmul(W,Pi,16)),(22,44,22,11),16)
    # j checks for the normalized two prime-to-29 2-isogenies.
    def j(a,b):
        c=fs(square(a),fscale(b,3))
        return fd(fscale(fm(square(c),c),256),fm(square(b),fs(square(a),fscale(b,4))))
    A2,B2=fe(6),fe(-3)
    assert j(A2,B2)==fe(2)
    r=fa(fe(-3),fscale(s,8))
    a=fa(fscale(r,3),A2)
    b=fa(fa(fscale(square(r),3),fscale(r,12)),B2)
    assert j(fscale(a,-2),fs(square(a),fscale(b,4)))==fe(25)
    ui=fscale(s,4)
    # actual Velu-normalized quotient coordinate of T4 kernel image:
    assert fa(fs(ui,fe(3)),fd(fe(3),ui))==r
    return (I,W,Pi,nu)

def latch(A,d):
    # d^2-layer, C=<d*T>, [d]^-1 C=<T,d*w*T>.
    m=d**2
    G=[[m if i==j else 0 for j in range(4)] for i in range(4)]
    for c in product(range(m),repeat=4):
        a=msum(A,c,m)
        if a[1][0]==0 and a[0][0]%d==0 and a[1][1]%d==0:
            G.append(list(c))
    assert len(G)==d**4+4
    H=hermite_normal_form(Matrix(G).transpose())
    assert int(H.det())==d**4
    return [list(map(int,H[:,i])) for i in range(4)]

def basis(H,d):
    return [[sum(F(x,d)*row[i] for x,row in zip(c,RQ)) for i in range(4)] for c in H]

def unmarked_vectors(B,D):
    # All raw quaternion coordinates have denominator |det_route|*3 <=12.
    L=1
    from math import lcm
    for b in B:
      for x in b:L=lcm(L,x.denominator)
    M=Matrix(B).transpose().inv()
    c=D*L*L
    # trace=0 gives y=2x; a norm=3x²; norm(b)=(2z-t)²/4+3t²/4.
    out=[]
    for a in range(-isqrt(c//3),isqrt(c//3)+1):
      n=c-3*a*a
      if n%29:continue
      v=n//29
      for t in range(-isqrt(4*v//3),isqrt(4*v//3)+1):
        X=4*v-3*t*t;x=isqrt(X)
        if x*x!=X:continue
        for u in {x,-x}:
          if (u+t)%2:continue
          r=[F(a,L),F(2*a,L),F((u+t)//2,L),F(t,L)]
          assert N(r)==D
          coeff=M*Matrix([(r[0]+1)/2,r[1]/2,r[2]/2,r[3]/2])
          if all(getattr(d,'q',0)==1 for d in coeff):out.append(r)
    return sorted(out)

def strmatrix(M):return [[str(c) for c in r] for r in M]
def main():
    A=tates(); tab={}; ds=(1,2,4)
    for j,d in zip((0,2,25),ds):
        H=latch(A,d);B=basis(H,d)
        G=[[N([x+y for x,y in zip(a,b)])-N(a)-N(b) for b in B] for a in B]
        assert Matrix(G).det()==29**2
        R=unmarked_vectors(B,119)
        tab[j]=dict(index_for_scaled_lattice=d**4,H=H,quaternion_basis=strmatrix(B),
                    trace_polar_gram=strmatrix(G),absolute_raw_119_vectors=len(R),
                    raw_119_vectors=strmatrix(R))
    assert [tab[j]['absolute_raw_119_vectors'] for j in (0,2,25)]==[12,8,8]
    for j in (0,2,25):
        raw=tab[j]['raw_119_vectors']
        lie=[r for r in raw if (F(r[0])-1).numerator%29==0]
        factor=3 if j==0 else 1
        assert len(lie)*2==len(raw) and len(lie)%factor==0
        tab[j]['normalized_raw_119_vectors']=lie
        tab[j]['unmarked_119_after_Lie_and_automorphisms']=len(lie)//factor
    print(json.dumps(dict(scope="Exact three maximal orders and full small shell; no level orientation or production coefficient.",tate_actions=A,orders=tab),indent=2,sort_keys=True))
if __name__=='__main__':main()
