from itertools import product
from math import gcd, prod
from fractions import Fraction

def crt(v, mod):
    M=prod(mod); return sum(a*(M//m)*(pow(M//m,-1,m) if m>1 else 0) for a,m in zip(v,mod))%M

def norm(z):a,b=z; return a*a+b*b

def rotate(x,y,M): return [(x%M,y%M),(-y%M,x%M),(-x%M,-y%M),(y%M,-x%M)]
def cls(z,M):return min(rotate(*z,M))
base=16*7
r=(crt((9,1),(16,7)),crt((0,3),(16,7)))
assert gcd(norm(r),base)==1
tests=0; fibre_sets=0
for P in [(),(3,),(5,),(3,5),(5,11),(3,5,11)]:
 M=base*prod(P)
 rest=[]
 for p in P:
    fiber={j:[] for j in range(1,p)}
    safe={j:[] for j in range(1,p)}
    for z in product(range(p),repeat=2):
        j=norm(z)%p
        if not j:continue
        fiber[j].append(z)
        if all(norm((z[0]+d,z[1]))%p for d in (-1,1)):safe[j].append(z)
    rest.append((fiber,safe))
 for n in product(*(range(1,p) for p in P)):
    vals=[]
    for mask in (0,1):
        actual=set()
        other=set()
        count=prod(len(t[mask][j]) for t,j in zip(rest,n))
        for x in product(*(t[mask][j] for t,j in zip(rest,n))):
            z=tuple(crt((r[i],*(w[i] for w in x)),(base,*P)) for i in range(2))
            assert gcd(norm(z),M)==1
            assert [(z[0]%p,z[1]%p) for p in P]==list(x)
            actual.add(cls(z,M)); other.add(cls((z[0],-z[1]),M))
            tests+=1
        assert not actual&other
        assert len(actual)==count
        vals.append(count)
    assert Fraction(vals[1],vals[0])==prod(Fraction(len(t[1][j]),len(t[0][j])) for t,j in zip(rest,n))
    fibre_sets+=1
print(f"PASS {fibre_sets} fixed norm cells, {tests} exact class assignments, no duplicate or conjugate collapse")
