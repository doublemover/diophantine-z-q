#!/usr/bin/env python3
"""Class obstruction of the actual control's p11 partial ideal, and fixed p19 support candidates."""
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
import json
r=Path(__file__).resolve().parents[2]

def pin(p,h):
 assert sha256((p/'SHA256SUMS').read_bytes()).hexdigest()==h
 for ln in (p/'SHA256SUMS').read_text().splitlines():
  x,n=ln.split();assert sha256((p/n).read_bytes()).hexdigest()==x
 return p
G=r/'rc-native-helper-20261120/ct-level48-oriented-sparse-gauss-cubic-r1';pin(G,'37906f4cc8dfab18706b6430d8e614befb67c0ed5a116f4a5de65c0e07a2802b')
T=r/'high-hom-1120/heegner-compressed-trace/original-D311-inert11-quadratic-projections-r1';pin(T,'c73012e9c6c2e17cbebd33d604e46f017b7e27f23f6e111962b67262b3586017')
X=json.loads((T/'EXACT-D311-P11-PROJECTIONS.json').read_text());Y=X['binary_projection']
assert X['D']==-311 and X['f']==241 and Y['5']['oriented_roots_and_exponents']==[[9,-80],[2,80]]
assert Y['1']['oriented_roots_and_exponents']==[[5,0],[6,0]] and Y['6']['unique_exponent']==Y['30']['unique_exponent']==0
E={};exec((G/'check_sparse_gauss_cubic.py').read_text().split('D=-421991;')[0],E)
D=-311; f=241; DM=D*f*5
K=E['Quad'](DM,(0,8));unit=K.unit

def state(p,r,e):return K.factorstate(p,r,e)[0]
def normexp(p,r,e):return K.mulstate(state(p,r,e),state(p,(1-r)%p,-e))

def check_order26(p,r):
 H=[state(p,r,e)[0] for e in (2,13,26)]
 assert H[0]!=unit and H[1]!=unit and H[2]==unit
 I=unit;P=((p,0),((-r)%p,1))
 for _ in range(26):I=K.rawmul(I,P)
 a,b=K.gauss(*I)[0];assert K.N((a,b))==p**26
 assert E['hnf']([(a,b),K.mul((a,b),(0,1))])==I
 return dict(exponents=[2,13,26],reduced=H,principal_generator=[a,b])
R11=check_order26(11,5);R19=check_order26(19,0)
N11=normexp(11,5,-80);assert N11[0]==((245,0),(177,1))!=unit
assert normexp(11,5,-80*13)[0]==unit
A19=normexp(19,0,6);assert K.mulstate(N11,A19)[0]==unit
assert normexp(19,0,13)[0]==unit and normexp(19,0,1)[0]!=unit

def chi(d,p):return 0 if d%p==0 else (-1 if pow(d%p,(p-1)//2,p)!=1 else 1)
L={p:[chi(D,p),chi(-5,p),chi(DM,p)] for p in (11,13,17,19)}
assert L[13][0]==1 and L[17][2]==-1 and L[19]==[-1,-1,1]
assert (2*((19-5)//2))%19==14 # u = 8s, s^2=2 is the named root of -5
assert (2*8*8)%19==(-5)%19 and 2*5*5%19==D%19 and 2*4*4%19==f%19
assert (2*5*4)%19==2 and 9**2%19==5 and 5**2%19==6
assert (9*2)%19==18 and (18+1)*pow(2,-1,19)%19==0
cases=[]
for x,a,b in ((112,3110,1679),(1024,2215,1942)):
 m=f*f*D*(-320)-x*x
 assert 0<m and m%19==0 and m%(19**2)!=0 and x%19==17 and x%16==0
 assert (f*5*(8*8)*2)%19==x%19 # named Lie dW*dU, U=8u
 assert Q(a*a+5*b*b,25)==Q(m,320*19)
 assert Q(x*x,-320)-19*Q(a*a+5*b*b,25)==f*f*D
 cases.append(dict(x=x,xmod32=x%32,m=m,v19=1,offdiagonal_numerator=[a,b],denominator=5))
print(json.dumps(dict(scope='actual control p11 projected class, and p19 arithmetic candidates only; no marked p19 exponent or original selected source',
 binary_discriminant=DM,p11_partial_HNF=N11[0],p11_class_order=13,class_order_11=26,class_order_19=26,
 q11=R11,q19=R19,p19_conditional_balanced_cancel_exponent_mod13=6,small_rational_prime_filters=L,p19_cases=cases),sort_keys=True,separators=(',',':')))
