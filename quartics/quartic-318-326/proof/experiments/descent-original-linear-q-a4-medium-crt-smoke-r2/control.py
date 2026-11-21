from fractions import Fraction as F
from itertools import product, permutations
from math import gcd, lcm, prod
from random import Random
rng = Random(318326)
signed=crt=maskcase=boxcnt=supportcase=observed=unitbox=0

def coords(m): return tuple(product(range(m),repeat=4))
def res(x,m): return tuple(t%m for t in x)
def idform(Q,u,q,k): return q if k is None else u+k*Q**2*q
def cs(Q,i,j,k):
    if i is None: return (1,0,1) if k is None else ((k-j)*Q**2,1,1)
    if j is None: return (0,1,1) if k is None else (1,(k-i)*Q**2,1)
    return (1,-1,(i-j)*Q**2) if k is None else (k-j,i-k,i-j)
def vals(x): return x[0]**2+x[1]**2,x[2]**2+x[3]**2
def key(C,x): 
    h,g=vals(x)
    return prod(abs(a*h+b*g) for a,b,_ in C)
def cross(x,p): return ((x[0]-1)**2+x[1]**2)%p==0 and ((x[2]+1)**2+x[3]**2)%p==0
def diagonal(x,p): return ((x[0]-1)**2+x[1]**2)%p==0 and ((x[0]+1)**2+x[1]**2)%p==0
for Q,u,q in product((-5,-1,1,2,5),(-11,0,17),(1,3,-5)):
    for i,j in permutations((None,-3,0,1,9),2):
        for k in (None,-3,0,1,9):
            a,b,d=cs(Q,i,j,k)
            assert d and a*idform(Q,u,q,i)+b*idform(Q,u,q,j)==d*idform(Q,u,q,k)
            observed+=1
for p in (3,5,7,11,13,17,19):
    for test,cap in ((cross,4),(diagonal,2)):
        O=[x for x in coords(p) if test(x,p)]
        assert len(O)<=cap*p*p
        if test==diagonal:
            assert all(x[0]==0 and (x[1]**2+1)%p==0 for x in O)
        maskcase+=1
for l,T in ((3,()),(3,(2,)),(5,(2,)),(7,(2,3)),(3,(2,5)),(5,(2,3)),(7,(3,5))):
    d=prod(T)
    C=[cs(2,None,1,k) for k in (None,-2,1,3)]
    A=tuple(x for x in coords(l) if cross(x,l))
    E=tuple(x for x in coords(d) if key(C,x)%d==0)
    assert len(E)==prod(sum(key(C,x)%p==0 for x in coords(p)) for p in T)
    supportcase+=1
    for r in range(520):
        x=tuple(rng.randrange(-5000,5001) for _ in range(4))
        rhs=all(key(C,res(x,p))%p==0 for p in T)
        assert (key(C,x)%d==0)==rhs
        joint=(res(x,l) in A) and rhs
        assert joint==((res(x,l) in A) and (res(x,d) in E))
        crt+=1
    for B in (l*d,l*d+7,2*l*d+15):
        L=2*B+1
        n=l*d
        a=[sum(j%n==r for j in range(-B,B+1)) for r in range(n)]
        assert all(abs(c-F(L,n))<=1 for c in a)
        f=[[next(t for t in range(n) if t%l==i and t%d==j) for j in range(d)] for i in range(l)]
        obs=sum(prod(a[f[i][j]] for i,j in zip(r,s)) for r,s in product(A,E))
        main=F(L**4*len(A)*len(E),l**4*d**4)
        assert abs(obs-main)<=F(1620*B**3*d,l)
        boxcnt+=1
        if n==l: unitbox+=1
for r in range(2000):
    P=rng.choice((1,2,3,6,10,15,30,42,105))
    z=rng.randrange(1,20)
    D=[d for d in range(1,z+1) if P%d==0]
    w={d: 1 if d==1 else rng.randrange(-d,d+1) for d in D}
    K=[rng.randrange(0,80) for _ in range(20)]
    c=lambda d: sum(k%d==0 for k in K)
    amp=lambda k: sum(w[d] for d in D if k%d==0)
    geom=sum(amp(k)**2 for k in K)
    exp=sum(w[d]*w[e]*c(lcm(d,e)) for d,e in product(D,repeat=2))
    assert geom==exp and sum(gcd(P,k)==1 for k in K)<=geom
    signed+=1
print(f'observed_numerators={observed} signed_coprime_squares={signed} modular_CRT={crt} exact_squarefree_density={supportcase} signed_box_main_errors={boxcnt} modulus_one={unitbox} cross_or_diagonal_caps={maskcase}')
