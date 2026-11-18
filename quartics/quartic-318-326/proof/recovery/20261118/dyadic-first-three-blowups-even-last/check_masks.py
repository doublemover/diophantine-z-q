from fractions import Fraction as F
from itertools import product
from collections import Counter
def val(x):
 x=F(x);assert x.denominator%2;x=abs(x.numerator);n=0
 while x%2==0: n+=1;x//=2
 return n
b=[F(z) for z in (0,32,76832,-343)]; c=[F(0),F(32),F(1120,3),F(375)];cnt=Counter()
for cfg,e in enumerate((b,c)):
 for D in product((-1,1),repeat=3):
  if len(set(D))==1:continue
  for a in (-1,1):
   d=max(set(D),key=D.count); j,k=[i for i in range(3) if D[i]==d];m=D.index(-d)
   H=d*(e[j]-e[k])/4;M=d*(e[m]-e[j])/2;f=a*(e[j]-e[3]);h=val(H)
   assert val(M)==4 and val(f)==0 and h==(8 if j==1 else 3)
   for n in (1,2,3):
    assert 2*h-2*n>=0 and 8-2*n>=2 and 2*(8-2*n)+2>=6
   cnt[3 if h==3 else 4]+=1
assert cnt=={3:16,4:8}
print('24 representatives, both contact configurations, all powers and final embedding-dimension partition verified')
