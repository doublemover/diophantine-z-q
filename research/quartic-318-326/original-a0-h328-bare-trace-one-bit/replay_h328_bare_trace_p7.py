#!/usr/bin/env python3
from hashlib import sha256
import json
from pathlib import Path

old = Path(__file__).resolve().parent.parent / "original-a0-h328-t18-known-nine-pure-second-r1"
raw = (old / "PINNED-OLD-T18-REPLAY.json").read_bytes()
assert sha256(raw).hexdigest() == "7c94388b54349fe6247aa8baace6cbba3f94db8f3c6e2f8e4717308d5cf96d0f"
j=json.loads(raw)
n,beta = j["squarefree_amplitude"], j["beta"]
u,v = j["first_point"]
p = 7
assert beta == 204618888056724185 and n == beta*(1-324*beta)*(1-2916*beta)
assert n%p==0 and n%(p*p)!=0 and u==beta*(1+972*beta)**2
assert v*v==u*(u-n)*(u+3*n)
D=j["D7"]
assert D==6 and pow(D,3,7)==6
s=2+p*(((-3-2*2)//p)*pow(4,-1,p)%p)
assert s==37 and (s*s+3)%(p*p)==0
r0,r1,r2=0,2*n*(1+s)%(p*p),2*n*(1-s)%(p*p)
assert [x%p for x in (r1,r2,r1-r2)]==[0]*3
assert all(x%(p*p) for x in (r1,r2,r1-r2))
# Specialized root values of the two differences (x-r0,x-r1).
pairs=[("O",[0,0]), ("T0",[0,1]), ("T1",[1,0]), ("T2",[1,1])]
def parity_nonzero_depth(value):
    assert value%(p*p)!=0
    return int(value%p==0)
def mul_parity(x,y):
    return parity_nonzero_depth(x)^parity_nonzero_depth(y)
assert pairs[1][1]==[mul_parity(r1,r2),parity_nonzero_depth(-r1)]
assert pairs[2][1]==[parity_nonzero_depth(r1),mul_parity(r1,r1-r2)]
assert pairs[3][1]==[parity_nonzero_depth(r2),parity_nonzero_depth(r2-r1)]
assert len({tuple(x) for _,x in pairs})==4
# The K-place is unramified and all roots are rational locally. The
# valuation classes are unchanged over K7. Conjugation fixes each class.
norm_classes=[[e^e,f^f] for _,(e,f) in pairs]
assert all(c==[0,0] for c in norm_classes) and pairs[1][1]!=[0,0]
print(json.dumps({"actual_h":328655617654071015360,"prime":p,"delta_mod7":D,
              "n_div_7_mod_7":n//p%p,"minus_three_square_root_mod49":s,
              "root_abscissas_mod49":[r0,r1,r2],"kummer_valuation_pairs":dict(pairs),
              "trace_mod_double_pairs":norm_classes,"T0_local_trace":False,
              "scope":"local 7 arithmetic only, no global bare trace/index"},indent=2))
