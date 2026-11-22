#!/usr/bin/env python3
"""Exact ordinary Cl^2/Frobenius orbit projection of the inert-29 cubic phase."""
import json
from hashlib import sha256
from itertools import combinations_with_replacement
from calibration_end_rings import root,m,fd,O,JS,class_info,sq_support,conductor
from hecke_seven_laurent import C7
c0={(0,0):2,(0,5):2,(1,1):-2,(2,4):-1,(3,3):2}
IJ=list(combinations_with_replacement(range(6),2))
CO=[c0.get(ij,0) for ij in IJ]
# On affine curve, y is short Y, not y48. Use old fixed phase.
def vals(X,Y):
    Z=m.add(Y,m.pw(X,4))
    return [1,Z,*[m.mul(m.pw(X,k),m.add(Z,7)) for k in range(1,5)]]
gamma=m.f(14,5); cube={m.pw(gamma,i):i for i in range(3)}
ref=root/'rc-native-helper-20261120/ct-level48-fixed103-inert29-tate-cubic-r1/EXACT-INERT29-TATE-CUBIC.json'
assert sha256(ref.read_bytes()).hexdigest()=='57c008b35c79fb8cf35ba5c77dd444b021120151a73dbaaace80b009a3631a7f'
rows=json.loads(ref.read_text())['all_flags']
M=[[0]*6 for _ in range(6)]
for (i,j),a in zip(IJ,CO):M[i][j]=M[j][i]=a%29
gweights=[]
for X,Y,*_,u,k in rows:
    v=vals(X,Y)
    w=[]
    for i in range(6):
       x=0
       for j in range(6):x=m.add(x,m.mul(M[i][j],v[j]))
       w.append(x)
    A=m.phi(X,Y); H=m.pm(4,m.p_add(A,m.p_neg(m.p_fr(A))))
    j=next(j for j in range(9) if m.pm(j,(14,m.f(0,13)))==H)
    assert j%3==k
    gweights.append((w,k))

def evalc(P,w): 
    r=0
    for x,y in zip(P,w):
        r=m.add(r,m.mul(x,y))
    assert r
    return cube[m.pw(r,560)]

T=m.roots_table()
C=list(m.curvepoints(T));SS={(X,Y) for X,Y,*_ in rows}
O=[Q for Q in C if m.j48(*Q) not in (None,0,2,25)]
assert all(all(q is not None for q in Q) for Q in O)
assert len(SS)==224 and len(O)==672 and not any(all(x<29 for x in P) for P in O)
assert SS=={Q for Q in C if m.j48(*Q) in (0,2,25)}
idx={(v[0],v[1]):i for i,v in enumerate(rows)}
flags=list(idx)
def w3(Q):
    X,Y=Q
    return m.div(28,X),m.div(m.neg(Y),m.pw(X,4))
def w16(Q):return m.w48(*w3(Q))
def ab(Q):
    return Q,w16(Q),w3(Q),m.w48(*Q)
sign=(1,1,-1,-1)
idxs=[tuple(idx[q] for q in ab(P)) for P in flags]
assert all([gweights[i][1] for i in row]==[(x*gweights[row[0]][1])%3 for x in sign] for row in idxs)
assert all((gweights[idx[m.q_fr(*P)]][1]+gweights[idx[P]][1])%3==0 for P in flags)
def vec(Q):
    P=vals(*Q);PF=vals(*m.q_fr(*Q))
    v=[(evalc(P,w)+evalc(PF,w))%3 for w,_ in gweights]
    return [sum(x*v[i] for i,x in zip(row,sign))%3 for row in idxs]
def gmat(C,JJ):
 M=[[0]*JJ for _ in range(JJ)]
 for (i,j),c in C.items():M[i][j]=M[j][i]=c%29
 return M
def vmat(M,Z):
 return [fun_sum([m.mul(M[i][j],z) for j,z in enumerate(Z) if M[i][j]]) for i in range(len(M))]
def fun_sum(Z):
 a=0
 for z in Z:a=m.add(a,z)
 return a
def point_data(D,C):
 arr=sorted(P for P in O if m.j48(*P) in JS and fd(P)==D)
 r={P:vals(*P) for P in arr};Qset=set(arr)
 t={P:vmat(gmat(C,6),vals(*P)) for P in arr}
 H={P:[Q for Q in arr if P!=Q and not fun_sum([m.mul(x,y) for x,y in zip(t[P],r[Q]) if x and y])] for P in arr}
 assert all(len(z)==2 for z in H.values())
 assert all(P in H[Q] for P,qs in H.items() for Q in qs)
 return Qset,H
def cycles(H):
 seen=set();out=[]
 for P in sorted(H):
   if P in seen:continue
   v=[P,H[P][0]]
   while True:
       n=next(Q for Q in H[v[-1]] if Q!=v[-2])
       if n==P:break
       v.append(n)
   assert not seen&set(v);seen.update(v);out.append(v)
 return out
def row_data(Qs,typ):
 out=[0]*len(flags)
 for Q in Qs:
   w=vec(Q)
   out=[(a+b)%3 for a,b in zip(out,w)]
 return out
def reduce(v,r):
 for i,a in sorted(r.items()):
    z=v[i]
    if z:v=[(x-z*y)%3 for x,y in zip(v,a)]
 return v
def linear(R):
 r={}
 for D,c,v in R:
    v=reduce(v,r)
    if any(v):
       i=next(i for i,x in enumerate(v) if x)
       r[i]=[(v[i]*x)%3 for x in v]
 rem=reduce([k for _,k in gweights],r)
 return len(r),sum(bool(x) for x in rem)

SPECS=[(-2880,C7,7,2,16),(-320,C7,7,2,8)]
info={};rs=[]
for D,CC,ell,sz,h in SPECS:
    order,ss,tau,sq=class_info(D)
    assert (order,ss)==(h,sz)
    H,S=sq_support(D,ell)
    assert len(H)==2 and all(x in sq for x in S) and set(S)|{(1,0,-D//4)}==sq
    _,graph=point_data(D,CC)
    cs=cycles(graph)
    C0=[frozenset(c[s::2]) for c in cs for s in range(2)]
    assert all(len(c)==2*sz for c in cs) and all(len(c)==sz for c in C0)
    seen=set();rows1=[]
    for c in sorted(C0,key=lambda c:sorted(c)):
        cF=frozenset(m.q_fr(*P) for P in c)
        assert cF in C0 and c!=cF
        if not c&seen:rows1.append(c)
        seen.update(c|cF)
    rs.extend((D,c,row_data(c,D)) for c in rows1)
    info[D]=dict(h=h,class_squares=sorted(sq),p29=tau,p_move=ell,p_move_forms=H,
        class_square_size=sz,ordinary_flags=len(graph),horizontal_cycles=len(cs),
        horizontal_cycle_size=2*sz,genus_frobenius_rows=len(rows1))
assert len(rs)==72

from itertools import product
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form as hnf
from math import lcm
def typ(D,c,N=16):
 s=D%2;K=(s*s-D)//4
 W=Matrix([[0,-K],[1,s]])
 un=[a for a in range(N) if a%2]
 def proj(P):return min((P[0]*u%N,P[1]*u%N) for u in un)
 lines=sorted({proj(x) for x in product(range(N),repeat=2) if any(a%2 for a in x)})
 tu=c*s;tn=c*c*K
 M=[(a,b) for a,b in product(range(N),repeat=2) if (a*a+tu*a*b+tn*b*b)%2]
 def mul(z,w):
    a,b=z;u,v=w
    return proj((a*u-tn*b*v,a*v+b*u+tu*b*v))
 def fp(z):
   a,b=z
   H=hnf(Matrix([[N,0,a],[0,N*c,b*c]]))
   J=H.inv()*W*H
   return lcm(*(int(x.q) for x in J))
 seen=set();res=[]
 for P in lines:
  if P in seen:continue
  O={mul(P,z) for z in M};seen|=O
  cons={fp(x) for x in O};assert len(cons)==1
  tru={q for a,b in O if (q:=proj((a+tu*b,-b))) in O and q==(a,b)}
  ic=proj((P[0]+tu*P[1],-P[1]))
  res.append((P,len(O),next(iter(cons)),bool(tru),ic in O))
 return res

LOCAL=((-20,4,2,((4,1),(4,3)),False),(-20,4,4,((0,1),(8,1)),True))
for D,c,d,L,real in LOCAL:
   r=[(i,sz,real0,same) for i,sz,f,real0,same in typ(D,c) if f==d]
   assert r==[(i,1,real,real) for i in L],(D,c,d,r)
from collections import defaultdict,Counter
Dgood=(-2880,-320)
GJ=defaultdict(list);CT=defaultdict(Counter)
for P in O:
    j=m.j48(*P)
    if j not in JS or fd(P) not in Dgood:continue
    D=fd(P); c=conductor(j);d=conductor(m.j48(*m.w48(*P)))
    CT[D][c,d]+=1
    GJ[D,j,d].append(P)
assert CT[-2880]=={(4,12):32,(12,4):32,(12,2):32,(4,6):32,(2,12):32,(6,4):32}
assert CT[-320]=={(4,2):32,(4,4):32,(2,4):32}
assert sq_support(-320,3)==([(3,-2,27),(3,2,27)],[(9,2,9)])
def t16(P):
    X,Y=P;Z=m.div(m.add(m.add(Y,m.pw(X,4)),1),2)
    return m.add(m.sub(X,2),m.div(m.mul(3,X),Z))
def cf(P,D):
    R=P;Ws=[]
    x=conductor(m.j48(*R));y=conductor(m.j48(*m.w48(*R)))
    if x%4:R=w16(R);Ws.append(w16)
    x=conductor(m.j48(*R));y=conductor(m.j48(*m.w48(*R)))
    if D==-2880 and x%3:R=w3(R);Ws.append(w3)
    j=m.j48(*R);x=conductor(j);y=conductor(m.j48(*m.w48(*R)))
    S=GJ[D,j,y]
    assert R in S
    if D==-2880:
        assert len(S)==2 and (x,y) in ((12,2),(12,4))
        P2=R if y==4 else next(Z for Z in S if Z!=R)
    else:
        assert D==-320 and len(S)==4 and (x,y) in ((4,2),(4,4))
        t3=m.j48(*w3(R));t2=t16(R)
        A=[Z for Z in S if m.j48(*w3(Z))!=t3 and ((t16(Z)==t2)==(y==4))]
        assert len(A)==1
        P2=A[0]
    for W in reversed(Ws):P2=W(P2)
    return P2
def orb(c):
    c=frozenset(c)
    return c|frozenset(m.q_fr(*P) for P in c)
group={orb(c):(D,c) for D,c,_ in rs}
real=defaultdict(set)
for A,(D,c) in group.items():
    J=orb(cf(P,D) for P in A)
    assert J in group and group[J][0]==D
    assert orb(cf(P,D) for P in J)==A
    real[D].add(A|J)
assert tuple(len(real[D]) for D in Dgood)==(32,12)
def calc(P):
    return row_data([Q for Q in P if Q<m.q_fr(*Q)],None)
S5={(5,D,c):calc(c) for D in Dgood for c in real[D]}
for ii,(P,(_,k)) in enumerate(zip(flags,gweights)):
    gweights[ii]=(vmat(gmat(C7,6),vals(*P)),k)
S7={(7,D,c):calc(c) for D in Dgood for c in real[D]}
VV=S5|S7
assert linear([(D,c,v) for (K,D,c),v in VV.items()])==(21,0)
W=[
 (5,-2880,[(281,274),(296,149),(557,700),(600,593)],1),
 (7,-2880,[(270,593),(313,700),(574,149),(589,274)],1),
 (7,-2880,[(281,274),(296,149),(557,700),(600,593)],1),
 (7,-320,[(81,614),(184,314),(314,68),(322,689),(525,196),(575,793),(677,575),(806,237)],1),
 (5,-2880,[(270,277),(313,170),(574,721),(589,596)],-1),
 (5,-2880,[(47,711),(390,530),(477,327),(830,160)],-1),
 (7,-2880,[(270,277),(313,170),(574,721),(589,596)],-1),
 (7,-320,[(64,237),(193,575),(295,793),(345,196),(548,689),(556,68),(686,314),(789,614)],-1),
]
z=[0]*len(flags)
for K,D,L,sgn in W:
    assert orb(L)==frozenset(L) and frozenset(cf(P,D) for P in L)==frozenset(L)
    v=VV[K,D,frozenset(L)]
    z=[(a+sgn*b)%3 for a,b in zip(z,v)]
assert z==[k for _,k in gweights]
assert [pow(x%29,14,29) for x in (2,3,5)]==[28,28,1]
print(json.dumps(dict(scope='Totally real CM-supported cubic receiver; no moving oriented ideal is evaluated.',
    ordinary_orbits=info,local_lines=LOCAL,rank=21,real_packets={D:len(real[D]) for D in Dgood},
    signed_whole_packets=W,field_squareclasses=[5,6],
    actual_endpoint_depth_pairs={D:[[c,d,n] for (c,d),n in sorted(v.items())] for D,v in CT.items()},
    modular_polynomial_7_coefficients=[[i,j,c] for (i,j),c in sorted(C7.items())],
    ordered_cubic_bit_sha256=sha256(bytes(z)).hexdigest()),sort_keys=True,indent=2))
