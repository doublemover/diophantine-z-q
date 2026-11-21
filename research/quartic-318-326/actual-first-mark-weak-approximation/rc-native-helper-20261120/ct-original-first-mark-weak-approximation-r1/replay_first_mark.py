"""An exact retained-local toy control, not a numerically realized source pole."""
from fractions import Fraction as Q
from math import isqrt,prod
import json

beta,theta,seed,t=17,13,323,1485
u=beta*t*t
A,B,C=1+3*u,4*beta*t,2*(1-3*u)
D=beta*(1-u)*(1-9*u)
X,Y=beta*A*A,beta*A*B*C
assert X-D==B*B and X+3*D==beta*C*C
assert X*(X-D)*(X+3*D)==Y*Y
assert Y and D>0
assert Q(B,beta*(2*A+C))==t

p0,p1=2635933,246637
assert all(all(p%k for k in range(2,isqrt(p)+1)) for p in (13,17,19,p0,p1))
n=prod((17,19,p0,p1)); sc=32
assert D==n*sc**2 and n%12==11 and n%13
x,y=Q(X,sc**2),Q(Y,sc**3)
assert y*y==x*(x-n)*(x+3*n)
assert x==beta*Q(A,sc)**2 and x-n==Q(B,sc)**2
assert x+3*n==beta*Q(C,sc)**2

def ord_unit(z,p):
    v=0
    while z%p==0:z//=p;v+=1
    return v,z
a=[]
for p in (2,3,13,17,19):
    de,du=ord_unit(D,p);se,su=ord_unit(seed,p)
    assert (de-se)%2==0
    if p==2: assert (du-su)%8==0
    else: assert pow((du*su)%p,(p-1)//2,p)==1
    a.append([p,de-se,du%(8 if p==2 else p),su%(8 if p==2 else p)])
assert all(pow(beta,(p-1)//2,p)==1 for p in (p0,p1))
# The first mark on the theta companion is unramified locally outside
# support. Its distinct extra prime belongs to beta's split support.
assert pow(beta,(theta-1)//2,theta)==1

j=Q((2**4*13)**3,2**8*3**2)
assert j==Q(35152,9)
print(json.dumps(dict(scope='exact retained-local first-point fixture, not original pole, companion point, or Sel2 cardinality',
                      t=t,D=D,n=n,removed_square_root=sc,first_point=[str(x),str(y)],
                      residue_controls=a,distinct_new_primes=[p0,p1],E1_j=str(j)),
                 indent=2,sort_keys=True))
