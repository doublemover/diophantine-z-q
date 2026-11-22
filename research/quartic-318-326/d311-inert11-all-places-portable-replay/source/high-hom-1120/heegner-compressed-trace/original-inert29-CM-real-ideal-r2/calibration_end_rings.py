import sys,math
from pathlib import Path
from collections import deque
from sympy import Matrix, factorint
from sympy.matrices.normalforms import hermite_normal_form as hnf
from hashlib import sha256
root=Path(__file__).resolve().parent.parents[2]
src=root/'high-hom-1120/heegner-compressed-trace/original-detectors-inert29-finite-receiver-r1/replay_inert29.py'
assert sha256(src.read_bytes()).hexdigest()=='e1f570297815f21b270374b01a5f0972ee0d1cb20f7123082de254e4318d08f5'
sys.path.insert(0,str(src.parent))
import replay_inert29 as m
p=29;q=p*p;L=90
def mul(a,b):
    r={}
    for i,v in a.items():
       for j,w in b.items():
           if i+j<=L:r[i+j]=(r.get(i+j,0)+v*w)%p
    return {i:a for i,a in r.items() if a}
def s(a,b):return {i:a.get(i,0)+b.get(i,0) for i in a.keys()|b.keys()}
A={0:1}
for i in range(1,L+1):A=mul(A,{i*j:(-1)**j*math.comb(24,j)%p for j in range(1+min(24,L//i))})
Am={0:1}
for n in range(1,L+1):Am[n]=-sum(A.get(i,0)*Am[n-i] for i in range(1,n+1))%p
E={0:1,**{k:240*sum(d**3 for d in range(1,k+1) if k%d==0)%p for k in range(1,L+1)}}
J={i-1:v for i,v in mul(mul(mul(E,E),E),Am).items()}
def qpoly(l):
    d=l+1
    D=[{0:1}]
    for i in range(d):D.append(mul(D[-1],J))
    B=[{i*l:v for i,v in a.items()} for a in D]
    ij=[(i,j) for i in range(d+1) for j in range(i,d+1) if j<d or i==0]
    V=[]
    for i,j in ij:
        a=mul(D[i],B[j]);V.append(a if i==j else s(a,mul(D[j],B[i])))
    piv={}
    for k in range(-d*d,2*d*d+1):
        w=[v.get(k,0)%p for v in V]
        for i,a in sorted(piv.items()):
            z=w[i]
            if z:w=[(v-z*x)%p for v,x in zip(w,a)]
        if any(w):
            i=next(i for i,a in enumerate(w) if a)
            piv[i]=[x*pow(w[i],-1,p)%p for x in w]
    assert len(piv)==len(ij)-1
    k=next(i for i in range(len(ij)) if i not in piv);t=[0]*len(ij);t[k]=1
    for i,w in sorted(piv.items(),reverse=True):t[i]=-sum(a*b for a,b in zip(w,t))%p
    u=pow(t[ij.index((0,d))],-1,p)
    assert all(not sum(a*v.get(k,0) for a,v in zip(t,V))%p for k in range(-d*d,2*d*d+1))
    C={(i,j):a*u%p for (i,j),a in zip(ij,t) if a}
    return [[C.get((min(i,j),max(i,j)),0) for i in range(d+1)] for j in range(d+1)]
def evalpol(a,j):
    r=0
    for a0 in reversed(a):r=m.add(m.mul(r,j),a0)
    return r
def remove(a,j):
    r=[a[-1]]
    for i in range(len(a)-2,0,-1):r.append(m.add(a[i],m.mul(j,r[-1])))
    r=list(reversed(r));assert not m.add(m.mul(j,r[0]),a[0])
    return r
S=m.roots_table();CUB=[m.pw(x,3) for x in range(q)]
O=[A for A in m.curvepoints(S) if m.j48(*A) not in (None,0,2,25)]
trace={}
for j in range(q):
 if j in (0,2,25):continue
 if j==17:A,B=28,0
 else:
    h=m.div(j,m.sub(17,j));A,B=m.mul(3,h),m.mul(2,h)
 t=-sum(len(S[m.add(m.add(CUB[x],m.mul(A,x)),B)])-1 for x in range(q))
 assert t%p
 v=t*t-4*q;dd=-math.prod(a for a,e in factorint(-v).items() if e%2)
 if dd%4!=1:dd*=4
 trace[j]=(abs(t),int(dd),math.isqrt(v//dd))
JS=[j for j in sorted(trace) if trace[j][1] in (-51,-20)]
def get_depth(l):
 polys=qpoly(l);N={}
 for j in JS:
    a=[evalpol(d,j) for d in polys]
    r=[]
    for z in JS:
        if trace[z]!=trace[j]:continue
        while len(a)>1 and not evalpol(a,z):
            r.append(z);a=remove(a,z)
    N[j]=r
    assert len(r)<=l+1
 h={j:0 for j in JS if trace[j][2]%l}
 V=[j for j in JS if trace[j][2]%l==0]
 qq=deque(j for j in V if len(N[j])<l+1)
 assert all(len(N[j])==1 for j in qq),(l,[(j,trace[j],N[j]) for j in qq])
 seen={j:0 for j in qq}
 while qq:
    j=qq.popleft()
    for z in N[j]:
       if z not in seen:
          seen[z]=seen[j]+1;qq.append(z)
 assert all(j in seen for j in V)
 for j in V:
    c=trace[j][2];k=0
    while c%l==0:c//=l;k+=1
    assert 0<=seen[j]<=k
    h[j]=k-seen[j]
 return h
a2=get_depth(2);a3=get_depth(3)
def conductor(j):
    c=trace[j][2]
    while c%2==0:c//=2
    while c%3==0:c//=3
    assert c==1
    return 2**a2[j]*3**a3[j]
def fd(P):
 j,k=m.j48(*P),m.j48(*m.w48(*P))
 assert trace[j]==trace[k]
 return trace[j][1]*(math.lcm(conductor(j),conductor(k))**2)
def reduce(a,b,c):
    while True:
        n=(a-b)//(2*a);a,b,c=a,b+2*a*n,c+b*n+a*n*n
        if a>c:a,b,c=c,-b,a;continue
        if a==c and b<0:b=-b
        return a,b,c
def fs(D):
    return [(a,b,(b*b-D)//(4*a)) for a in range(1,math.isqrt(-D//3)+1) for b in range(-a+1,a+1)
            if (b*b-D)%(4*a)==0 and (b*b-D)//(4*a)>=a and (a!=(b*b-D)//(4*a) or b>=0)
            and math.gcd(a,b,(b*b-D)//(4*a))==1]
def comp(F,G,D):
    a,b,c=F;d,e,f=G;t=D%2
    x=-(b+t)//2;y=-(e+t)//2
    H=hnf(Matrix([[a*d,a*y,d*x,x*y+(D-t*t)//4],[0,a,d,x+y+t]]))
    k=math.gcd(*[int(x) for x in H])
    A,u,g=[int(H[i,j])//k for i,j in ((0,0),(0,1),(1,1))]
    assert g==1
    B=-t-2*u
    assert (B*B-D)%(4*A)==0
    return reduce(A,B,(B*B-D)//(4*A))
def class_info(D):
 forms=fs(D);O0=reduce(1,D%2,((D%2)-D)//4)
 h={reduce(29,b,(b*b-D)//116) for b in range(-28,30) if (b*b-D)%116==0}
 sq={comp(Q,Q,D) for Q in forms}
 assert sq<=set(forms)
 assert all(comp(Q,O0,D)==Q for Q in forms)
 assert len(h)==1 and all(comp(Q,Q,D)==O0 for Q in h),(D,h)
 assert not (sq & h)
 return len(forms),len(sq),list(h)[0],sq
def sq_support(D,ell):
 H={reduce(ell,b,(b*b-D)//(4*ell)) for b in range(-ell+1,ell+1) if (b*b-D)%(4*ell)==0}
 H={r for r in H if math.gcd(*r)==1}
 sq={comp(Q,Q,D) for Q in H}
 return sorted(H),sorted(sq)
