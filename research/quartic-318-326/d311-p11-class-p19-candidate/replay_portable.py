#!/usr/bin/env python3
"""Run the checked arithmetic with the exact upstream summary, not its arc table."""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
import json
r=Path(__file__).resolve().parent

def digest(p):return sha256(p.read_bytes()).hexdigest()
A=r/'author'; I=r/'input'; G=r/'exact-replay-donor'
assert digest(A/'SHA256SUMS')=='bf1163c367cb2e9d7630f24ccb86c549c7fecb5e5467fb5fdc312908ff39be5d'
for ln in (A/'SHA256SUMS').read_text().splitlines():
 h,n=ln.split();assert digest(A/n)==h
U=I/'UPSTREAM-P11-SHA256SUMS.txt'
assert digest(U)=='c73012e9c6c2e17cbebd33d604e46f017b7e27f23f6e111962b67262b3586017'
H={n:d for d,n in (s.split() for s in U.read_text().splitlines())}
P=I/'EXACT-D311-P11-PROJECTIONS.json';assert digest(P)==H[P.name]
assert digest(G/'check_sparse_gauss_cubic.py')=='7e67aee6cfede19c6be5236c335e09c5e52c671405c97b67aaed48a09190c4fd'
X=json.loads(P.read_bytes());Y=X['binary_projection']
assert X['D']==-311 and X['f']==241 and Y['5']['oriented_roots_and_exponents']==[[9,-80],[2,80]]
assert Y['1']['oriented_roots_and_exponents']==[[5,0],[6,0]] and Y['6']['unique_exponent']==Y['30']['unique_exponent']==0
# Apart from the exact input locator just checked, execute byte-identical signed arithmetic.
a=A/'check_D311_p11_order13_p19_candidate.py';marker='E={};exec('
text=a.read_text()
assert text.count(marker)==1
exec(compile(marker+text.split(marker,1)[1],str(a),'exec'))
