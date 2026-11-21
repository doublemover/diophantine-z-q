#!/usr/bin/env python3
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent
source=Path(sys.argv[1]) if len(sys.argv)>1 else D.parent/'linked-detector-four-root-norm-odd-guard-r1/EXACT-CHECKED-ODD-GUARDS.json'
raw=source.read_bytes()
assert sha256(raw).hexdigest()=='21dae4a50d7d7cda3bfab95d28951ab48355d71242ce7adea9bc084a972f4b64'
old=json.loads(raw)
roots=[F(-1,2),F(-1),F(-32,407),F(1,2399)]
u=[F(1),F(1,2)]
a=[(r+s)/2 for r,s in zip(roots[::2],roots[1::2])]
ds=[(r-s)/2 for r,s in zip(roots[::2],roots[1::2])]
K=[(ui**4-2*ai*ui*ui+di*di)/2 for ui,ai,di in zip(u,a,ds)]
L=[K[i]/u[i]**2 for i in range(2)]
assert L==[F(41,32),F(1275400596441,7626746323592)]
x=F(35441651962058444737857,55614360877956828839800)
y=F(183352115295979214553073483792738784397,184873626882008858208518823599138314000)
assert y*y==x*(x+L[0])*(x+L[1])
d=8*407*2399
X,Y=x*d*d,y*d**3
A,B=(int(D*d*d) for D in L)
assert [A,B]==[D*d*d for D in L]
assert Y*Y==X*(X+A)*(X+B)
p=71
assert (2*A*B*(A-B))%p!=0 and X.numerator%p and X.denominator%p**2==0 and X.denominator%p**3!=0
small={2:600,3:8,5:4,7:4,11:4,17:1,37:4,2399:4}
cells=[p for p,_,_ in old['archived_cells_and_distinct_scaled_root_units']]
assert len(set(cells))==19 and all(p not in small for p in cells)
assert all((2*A*B*(A-B))%p for p in cells)
# Exact input bounds for choosing a sufficiently high congruence multiple
# of P in the formal group at every place. The proof only needs existence.
arr=lambda f:[F(f).numerator,F(f).denominator]
out=dict(u=list(map(arr,u)),Lambda=list(map(arr,L)),P=[arr(x),arr(y)],
          integral_scale=d,integral_shifts=[A,B],integral_P=[arr(X),arr(Y)],
          exact_nontorsion_prime=p,scaled_discriminant=(16*A*A*B*B*(A-B)**2),
          minimum_small_seed_dyadic_odd_depths=small,good_cell_primes=cells)
print(json.dumps(out,indent=2))
