"""Exact 8x8 Hasse-Witt and finite-field order certificate, standard library."""
import json
from math import comb

p=19
g=8
def coeff(n):
    return sum((-1)**(9-a)*comb(9,a)*comb(9,b)
               for b in range(10) for a in [n-16*b] if 0<=a<=9)%p
H=[[coeff(p*i-j) for j in range(1,g+1)] for i in range(1,g+1)]
def mm(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(g))%p
             for j in range(g)] for i in range(g)]
T=H
tr=[]
for _ in range(g):
    tr.append(sum(T[i][i] for i in range(g))%p)
    T=mm(T,H)
# Newton/Faddeev-LeVerrier; k=1,...,8 invertible at 19.
P_desc=[1]
for k in range(1,g+1):
    P_desc.append(-pow(k,-1,p)*sum(P_desc[k-j]*tr[j-1]
                                      for j in range(1,k+1))%p)
assert P_desc==[1,17,10,3,15,13,2,18,7]
# Independent trace check in the original prime field.
N=1+sum(int(y*y%p==((x-1)*(pow(x,16,p)+1))%p)
        for x in range(p) for y in range(p))
assert (p+1-N)%p==tr[0]
def trim(a):
    a=[v%p for v in a]
    while a and a[-1]==0: a.pop()
    return a
def sub(a,b):
    return trim([(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])
def mul(a,b):
    if not a or not b: return []
    h=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b): h[i+j]+=v*w
    return trim(h)
def rem(a,b):
    a=a[:]
    d=pow(b[-1],-1,p)
    while len(a)>=len(b):
        a=sub(a,[0]*(len(a)-len(b))+[(d*a[-1]*w)%p for w in b])
    return a
def gcd(a,b):
    while b: a,b=b,rem(a,b)
    return trim([v*pow(a[-1],-1,p) for v in a])
def power(a,n,mod):
    b=[1]
    while n:
        if n&1: b=rem(mul(b,a),mod)
        n//=2
        if n: a=rem(mul(a,a),mod)
    return b
X=[0,1]
factors=[[11,6,13,18,1],[11,6,15,18,1]]
assert mul(*factors)==P_desc[::-1]
orders=[]
totients=[]
small_checks=[]
group_order=19**4-1
assert group_order==2**4*3**2*5*181
for F in factors:
    assert power(X,19**4,F)==X
    assert gcd(sub(power(X,19**2,F),X),F)==[1]
    y=[0,pow(4,-1,p)]
    n=group_order
    for r in (2,3,5,181):
        while n%r==0 and power(y,n//r,F)==[1]:
            n//=r
    assert power(y,n,F)==[1]
    rows=[]
    phi=n
    for r in (2,3,5,181):
        if n%r==0:
            w=power(y,n//r,F)
            assert w!=[1]
            rows.append([r,w])
            phi=phi//r*(r-1)
    orders.append(n)
    totients.append(phi)
    small_checks.append(rows)
assert orders==[16290,8145] and totients==[4320,4320]
print(json.dumps(dict(p=p,g=g,HW_matrix=H,point_count_F19=N,
                      charpoly_descending=P_desc,factors_ascending=factors,
                      ratio_root_orders=orders,ratio_root_totients=totients,
                      order_prime_factor_witnesses=small_checks,
                      maximum_exact_cyclotomic_degree=2*(2*g)),indent=2))
