#!/usr/bin/env python3
"""Fixed old arithmetic, and a same-beta but nonproduction negative-row control."""
from math import gcd,isqrt,prod
import json
P=(5,11,17,163,661,733,1489,1861)
V=(131,6551,2470991,16782959)
beta=prod(P)
assert beta==204618888056724185
D=5428178401
C=D**2-144*beta
F=(53,16470087437)
assert C==prod(F)==872914634161
def prime(p):
    return p>=2 and all(p%q for q in range(2,isqrt(p)+1))
assert all(prime(p) for p in P+F)
# The four actual visible theta factors' symbols were already pinned in the donor; 
# computing those symbols needs only Euler/Fermat on those certified primes.
def bit(a,p):
    s=pow(a%p,(p-1)//2,p)
    assert s in (1,p-1)
    return int(s==p-1)
assert gcd(D,6*beta)==1 and gcd(C,D*beta*6)==1 and C>0
assert beta%24==17 and C%24==1 and all(bit(-3,p)==1 for p in F)
S=tuple(p for p in P if bit(-3,p)==0)
assert S==(163,661,733,1489,1861)
cols=(-1,3)+P
rows=[sum(bit(beta//p if q==p else q,p)<<j for j,q in enumerate(cols)) for p in S]
rows.append(sum((q%4==3)<<j for j,q in enumerate(cols)))
def rank(X):
    rows={}
    for x in X:
        while x:
            j=x.bit_length()-1
            if j not in rows:
                rows[j]=x
                break
            x^=rows[j]
    return len(rows)
assert rank(rows)==6
e=-18444371
assert e==(-1)*11*17*1861*53 and e%4==1
d=beta*C
assert all((bit(e//p,p)==bit(d//p,p) if e%p==0 else bit(e,p)==0) for p in S)
f=(abs(e)//gcd(abs(e),6*beta))
assert f==53 and bit(3,53)==1
# Check the no-new-split case: for any alias of a fresh column's five old
# symbols and its mod-4 row, the ten old variables contain a correction.
surj={sum(((mask&z).bit_count()%2)<<j for j,z in enumerate(rows)) for mask in range(1<<len(cols))}
assert surj==set(range(64))
print(json.dumps(dict(beta=beta,actual_visible_theta=list(V),
   actual_visible_theta_three_bits=[bit(3,p) for p in V],
   old_split_primes=list(S),old_columns=list(cols),old_rows=rows,
   rank_and_columns=[6,10],all_old_admissions_correctable=len(surj),
   control=dict(denominator_D=D,C=C,theta_primes=F,e=e,
                three_bits=[bit(3,p) for p in F],
                d=str(d),cassels_sign=-1),
   scope='same beta standalone chart obstruction; no literal unseen support or rational point'),indent=2,sort_keys=True))
