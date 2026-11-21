from itertools import product, permutations
from random import Random
from fractions import Fraction as Q
rng=Random(318326)
norms=counts=detchecks=duals=0
for p in (3,5,7,11,13,17,19,23,31,43):
    chi=1 if p%4==1 else -1
    C=[0]*p
    for x,y in product(range(p),repeat=2): C[(x*x+y*y)%p]+=1
    A=p+(p-1)*chi
    assert C==[A]+[p-chi]*(p-1)
    norms+=p
    for K in range(1,p):
        s=sum(C[t]*C[K*t%p] for t in range(p))
        assert s==p**3+p*p-p
        counts+=1
    for r in range(2,min(p+2,9)):
        S=[(1,0),(0,1)]+[(1,h) for h in rng.sample(range(1,p),r-2)]
        for (a,b),(c,d) in permutations(S,2):
            assert (a*d-b*c)%p
            detchecks+=1
        E=sum(C[t]*C[u] for t,u in product(range(p),repeat=2) if any((a*t+b*u)%p==0 for a,b in S))
        total=2*A*p*p+(r-2)*(p**3+p*p-p)-(r-1)*A*A
        assert E==total
        assert abs(Q(E,p**4)-Q(r+2*chi,p))<=Q(6*r,p*p)
        duals+=1
print('checked_norm_cells',norms,'scaled_rank_four',counts,'distinct_minors',detchecks,'exact_common_core_unions',duals)
