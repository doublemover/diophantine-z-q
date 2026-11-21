from itertools import combinations
from math import lcm, factorial
import json

B=(0,32,76832,-343)
gaps=[abs(x-y) for x,y in combinations(B,2)]
D=lcm(*gaps)
assert D==2765952000
pmin={2:5,3:1,5:2,7:3}
def v(n,p):
    assert n
    s=0
    while n%p==0:
        n//=p
        s+=1
    return s
rows=[]
for p,m in pmin.items():
    classes=[[b for b in B if b%p==k] for k in range(p)]
    triple,=filter(lambda s:len(s)>1,classes)
    depths=sorted(v(a-b,p) for a,b in combinations(triple,2))
    assert len(triple)==3 and depths[0]==m
    # Finite controls over prime-field integer residue representatives only;
    # the proof's gap bound is independent of residue field.
    mod=p**(m+1)
    trunc=lambda n: min(v(n,p),m+1) if n else m+1
    tests=sorted(set(tuple(sorted(trunc(t-b) for b in B)[:2]) for t in range(mod)))
    assert all(a==0 and d<=m for a,d in tests)
    rows.append(dict(prime=p,triple=triple,gap_depths=depths,
                     representative_count=mod,first_two_controls=tests))
n=D
for p in pmin:
    n//=p**v(n,p)
assert n==1
E=3*5**2*7**3
assert E==25725
assert all(b%32==0 for b in rows[0]['triple'])
exp_lower_num=sum(720//factorial(i) for i in range(7))
assert exp_lower_num==1957
bounds=[]
for k,power in [(1,23),(4,22)]:
    C,rem=divmod(k*D**2,E)
    assert rem==0
    M,rem=divmod(420*512*D**2,C)
    assert rem==0
    margin=exp_lower_num**power-M*720**power
    assert margin>0
    bounds.append(dict(dyadic_gain=k,finite_common_scalar=C,
                       arch_after_finite_gain=M,strict_offset=power,
                       exact_exp_lower_margin=margin))
print(json.dumps(dict(contacts=B,ordered_gaps=gaps,D0=D,E=E,rows=rows,bounds=bounds),indent=2))
