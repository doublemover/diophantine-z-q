#!/usr/bin/env python3
from pathlib import Path
from math import isqrt,prod
import hashlib,json
W=Path(__file__).resolve().parents[3]
rc=W/'rc-native-helper-20261120'
paths=[rc/'ct-original-scalar-mestre-marked-selmer-r1'/'EXACT-MARKED-SELMER-ROWS.json',
       rc/'ct-original-scalar-zero-ordinate-boundary-r1'/'EXACT-ZERO-ORDINATE-CONTROLS.json']
P,C=[json.loads(p.read_text()) for p in paths]
pins={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
assert pins['EXACT-ZERO-ORDINATE-CONTROLS.json']=='5634e70486921a0ba63fb01239456cca51f558b73e3eec5e54ea821a87fcbacf'
assert pins['EXACT-MARKED-SELMER-ROWS.json']=='27ed493d157316f08a1958524778c0619e21f29fd0e6d079c90db869cb4570fc'
S=P['visible']; beta=prod(S[:8]); T=prod(S[8:])
h=P['h']; B=204618888056724185
assert beta==B and T==35589230039008870789 and T%24==13
for p in S:
    assert all(p%q for q in range(2,isqrt(p)+1))
A=dict(zip(S,P['conditional_one_unseen']['aggregate_bits']))
diag=dict(zip(S,P['true_d_stripped_bits']))
def bit(a,p):
    s=pow(a%p,(p-1)//2,p); assert s in (1,p-1)
    return int(s==p-1)
n=len(S)+2
U=len(S); edge=U+1
rows=[]
for j,p in enumerate(S):
    w=sum((diag[p] if q==p else bit(q,p))<<k for k,q in enumerate(S))+(A[p]<<U)
    rows += [w^(bit(3,p)<<edge)^(bit(-3,p)<<(n+j)),
             (w<<n)^(bit(2,p)<<(n+edge))^(bit(-1,p)<<(n+j))]
# Products over all hidden primes, not prime-by-prime substitution.
w=sum(A[p]<<k for k,p in enumerate(S))
w^=((w.bit_count()%2)<<U)
rows += [w,(w<<n)^(1<<(n+edge))]
# All hidden products together are 13 mod 24.
rows += [sum(bit(p,3)<<(n+k) for k,p in enumerate(S))^(1<<(n+edge)),
         sum((p%4==3)<<k for k,p in enumerate(S))^(1<<edge)^(1<<(n+edge)),
         sum((p%8 in (5,7))<<k for k,p in enumerate(S))^(1<<U)^
             sum((p%4==3)<<(n+k) for k,p in enumerate(S))]
assert rows==C['one_unseen_rows']
def rank(X):
    B={}
    for x in X:
        while x:
            k=x.bit_length()-1
            if k in B:x^=B[k]
            else:B[k]=x;break
    return len(B)
tests=C['tests']
def mask(i):
    j=0
    for col,p in enumerate(S+[None,3]):
        if p in tests[i]['first_primes']:j^=1<<col
    for col,p in enumerate(S+[None,2]):
        if p in tests[i]['second_primes']:j^=1<<(n+col)
    return j
basis=[255,((1<<(len(S)+1))-1)^255,mask(0),mask(1)]
assert rank(rows)==24 and rank(basis)==4
assert all((x&r).bit_count()%2==0 for x in basis for r in rows)
J=sum(1<<i for i in range(8))+(1<<edge)+(1<<U)
restrict=J|(J<<n)
vis=sum(1<<i for i in range(8,len(S)))
whole=lambda r: (r^(((r&vis).bit_count()%2)<<U)^(((r&(vis<<n)).bit_count()%2)<<(n+U)))&restrict
assert rank([whole(r) for r in rows[:24]+rows[26:]])==18
assert rank([whole(r) for r in rows])==18
pureS=[p for p in S[:8] if not bit(-3,p)]
assert pureS==[163,661,733,1489,1861]
assert all(bit(-3,p) for p in S[8:])
pureMask=sum(1<<(n+i) for i,p in enumerate(S) if p in pureS)
pureRank=rank([r&pureMask for r in rows[:24]+rows[26:]])
assert pureRank==len(pureS)==5
assert rank([x%2**n for x in basis])==4

# The auxiliary prime used solely to remove the finite unit phases.
p=1186981
assert p%24==13 and all(p%q for q in range(2,isqrt(p)+1))
assert [bit(p,q) for q in S]==[A[q] for q in S]
z=[t[key] for t in tests for key in ('r','s')]
assert all(bit(v,p)==0 for v in z)
R=4376874610839020
I0=1408921722900
J0=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000
ii=pow(6,15,I0)*pow(3,65536,I0)*J0%I0
assert bit(2,p)==1
def f(a,b=0):return a%p,b%p
z0=f(0)
def add(x,y):return f(x[0]+y[0],x[1]+y[1])
def sub(x,y):return f(x[0]-y[0],x[1]-y[1])
def prod2(x,y):return f(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def sq(x):return prod2(x,x)
def norm(x):return (x[0]*x[0]-2*x[1]*x[1])%p
def inv(x):
    q=pow(norm(x),-1,p)
    return f(q*x[0],-q*x[1])
def div(x,y):return prod2(x,inv(y))
D=sq(f(3,-1))
P0=f(1,1),f(0,2)
assert sq(P0[1])==prod2(P0[0],sub(sq(P0[0]),D))
def plus(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u:
        if add(y,v)==z0:return None
        assert y==v
        ell=div(sub(prod2(f(3),sq(x)),D),prod2(f(2),y))
    else:ell=div(sub(v,y),sub(u,x))
    xx=sub(sub(sq(ell),x),u)
    yy=sub(prod2(ell,sub(x,xx)),y)
    assert sq(yy)==prod2(xx,sub(sq(xx),D))
    return xx,yy
def times(m):
    A=None;Q=P0
    while m:
        if m%2:A=plus(A,Q)
        Q=plus(Q,Q);m//=2
    return A
assert times(I0) is None
def chart(P):
    x,y=P
    return div(prod2(f(2),y),add(sq(x),D))
u,v=chart(times(h%I0)),chart(times(ii))
H=norm(u);I=norm(v);r=pow(R,-1,p)
N=(1+(H*r)**2+2*sq(u)[0]*r)%p
Q=I*pow(H,-1,p)*pow(r,15,p)%p
W0=(N*N+R*Q*Q)%p
c=12*W0*pow(1+2448*B,-1,p)%p
delta=(1-B*c*c)%p
assert (delta,c,W0,H,I)==(557122,322463,121437,490579,221735)
print(json.dumps(dict(donor_sha256=pins,beta=B,visible_theta_product=T,
    fixed_rows=24,aggregate_rows=rows,basis=basis,aggregate_rank=24,
    beta_and_full_theta_rank=18, old_pure_second_rank=pureRank,
    old_pure_second_primes=pureS, aggregate_first_projection_rank=4,
    norm_receiver=dict(auxiliary_prime=p,square_classes=z,actual_h_chart=u,actual_i_chart=v,
         reduction_annihilator=I0,W=W0,c=c,delta=delta),
    scope='actual compact aggregate receiver, no field norms or boundary Cassels signs computed'),sort_keys=True,indent=2))
