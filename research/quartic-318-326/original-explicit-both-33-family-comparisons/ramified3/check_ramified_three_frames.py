from itertools import product
import json

F=tuple(product(range(3),repeat=2))
z=(0,0)
o=(1,0)
def add(u,v): return ((u[0]+v[0])%3,(u[1]+v[1])%3)
def mul(u,v):
    a,b=u;c,d=v
    return ((a*c-b*d)%3,(a*d+b*c)%3)
def sigma(u): return (u[0],-u[1]%3)
assert all(mul(mul(x,x),x)==sigma(x) for x in F)
R=tuple(product(F,repeat=2))
idx={x:i for i,x in enumerate(R)}
zero=idx[(z,z)]
one=idx[(o,z)]
P=idx[(z,o)]
tab=[]
for a,b in R:
    tab.append([idx[(mul(a,c),add(mul(a,d),mul(b,sigma(c))))] for c,d in R])
assoc=0
for i in range(81):
    for j in range(81):
        for k in range(81):
            assert tab[tab[i][j]][k]==tab[i][tab[j][k]]
            assoc+=1
rad=[i for i,x in enumerate(R) if x[0]==z]
assert len(rad)==9 and all(tab[i][j]==zero for i in rad for j in rad)
units=[i for i,x in enumerate(R) if x[0]!=z]
assert len(units)==72
for p in rad:
    if p==zero: continue
    assert {i for i in range(81) if tab[p][i]==zero}==set(rad)
for i in range(81):
    assert (len({tab[j][i] for j in range(81)})==81)==(i in units)
    inv=[j for j in range(81) if tab[i][j]==tab[j][i]==one]
    assert len(inv)==(1 if i in units else 0)
print(json.dumps({"actors":81,"products":81**2,"associativity_checks":assoc,
    "Pi_index":P,"nonzero_radical_kernel_tests":len(rad)-1,
    "non_generators":len(rad),"left_cyclic_generators":len(units),
    "two_sided_inverse_tests":81},indent=2,sort_keys=True))
