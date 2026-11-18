from itertools import product
from collections import Counter
cnt=Counter()
for q in product((1,-1,2,-2),repeat=4):
 if abs(q[3])!=1:continue
 p=[abs(x)==2 for x in q[:3]]
 if not (len(set(p))==2 or all(p) and len(set(q[:3]))>1):continue
 from fractions import Fraction as F
 cls=lambda x: (x<0,abs(x) in (F(2),F(1,2)))
 v=[cls(F(q[i],q[0])) for i in (1,2)];span={(False,False)}
 for a,b in v:span|={(a^j,b^k) for j,k in list(span)}
 K='G' if span=={(False,False),(True,False)} else ('Q' if len(span)==4 else 'S')
 cnt[K,q[3]]+=1
assert sum(cnt.values())==108 and cnt['G',1]==cnt['G',-1]==6
print('remaining odd-last corners by K and fourth sign',sorted(cnt.items()))
