"""Exact necessary local conditions for four squares, independently replayed."""
from pathlib import Path
from hashlib import sha256
import json

parent=Path(__file__).resolve().parents[1]
row=parent/"original-d210-arithmetic-four-root-constants-r1/EXACT-D210-TWISTS.json"
assert sha256(row.read_bytes()).hexdigest()=="24c76a69d42bac3ae3bd0eee0c73d2e9664403ea0bb669aef504ebfb776bb5a4"
data=json.loads(row.read_bytes())
B,C=data["contacts"],data["twists"]

def val(n,p):
    e=0
    while n%p==0: n//=p;e+=1
    return e

def local_unit_square(a,p):
    n=8 if p==2 else p
    return a%n in {i*i%n for i in range(n) if i%p}

out=[]
for p in (2,3,5,7):
    e=[val(c,p) for c in C]
    if p==5:
        assert len(set(e))==1
        ratio=C[2]*pow(C[1],-1,5)%5
        assert not local_unit_square(ratio,5)
        neg={"ratio_non_square":ratio}
    else:
        assert len({x%2 for x in e})>1
        neg={"multiplier_valuations":e}
    vals=[]
    n=8 if p==2 else p
    for t in range(n):
        a=[C[i]*(t-B[i]) for i in range(4)]
        fail=[]
        for i,x in enumerate(a):
            # If t class fixes the valuation strictly below precision,
            # test parity and, once enough residue digits are fixed, unit.
            if t%p!=B[i]%p and e[i]%2: fail.append([i,"odd_depth"])
            if x%p and not local_unit_square(x,p): fail.append([i,"unit_nonsquare"])
        if p==2 and t==4:
            assert val(t-B[0],2)==2 and e[0]==1
            fail.append([0,"depth_3"])
        if p==5 and t!=2:
            assert C[2]*(t-B[2])%5==ratio*(C[1]*(t-B[1]))%5
            assert a[1]%5 and a[2]%5
            fail.append([2,"unit_ratio_nonsquare"])
        assert fail,(p,t)
        vals.append({"t":t,"obstructions":fail})
    out.append({"p":p,"pole_case":neg,"integral":vals})
assert C[0]<0<C[2] and B[0]<B[2]
print(json.dumps({"scope":"nonbranch selected coarse point at same t",
  "local":out,"real":[[C[0],B[0]],[C[2],B[2]]]},indent=2))
