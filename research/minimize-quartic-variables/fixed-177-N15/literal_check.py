"""Read the ASCII polynomial independently; reconstruct sum of squares by triangular convolution."""
from pathlib import Path
from collections import Counter
from math import gcd
from hashlib import sha256
from itertools import combinations_with_replacement
import re,json
D=Path(__file__).resolve().parent
raw=(D/'quartic177-N15.txt').read_bytes(); s=raw.decode('ascii')
p={}; n=0
for t in re.finditer(r'[+-]?[^+-]+',s):
 assert t.start()==n;n=t.end()
 a=t[0];sg=-1 if a[0]=='-' else 1
 v=a.lstrip('+-').split('*');c=sg*(int(v.pop(0)) if v[0].isdigit() else 1)
 m=[]
 for k in v:
  u=re.fullmatch(r'x([1-9]\d*)(?:\^([2-4]))?',k);assert u
  m+=[int(u[1])]*int(u[2] or 1)
 key=tuple(m);assert c and key==tuple(sorted(key)) and key not in p;p[key]=c
assert n==len(s) and {i for m in p for i in m}==set(range(1,178)) and p[(1,1,1,1)]==1
r=json.loads((D/'QUADRICS.json').read_bytes());q=Counter();assert len(r)==149
for item in r:
 tr=item['terms'];assert all(len(m)<=2 for m,c in tr) and gcd(*(c for m,c in tr))==1
 for (m,c),(k,d) in combinations_with_replacement(tr,2):q[tuple(sorted(m+k))]+=c*d*(1 if m==k else 2)
assert p=={m:k for m,k in q.items() if k}=={tuple(m):k for m,k in json.loads((D/'POLYNOMIAL.json').read_bytes())}
assert len(p)==3503 and max(abs(k).bit_length() for k in p.values())==1615 and len(raw)==99403
assert sha256(raw).hexdigest()=='4c323791cffe8bda212b000641f595c9530d58eec5a1ba3e2a784396ff53ec56'
print('PASS independent stdlib literal parser, 149-row convolution, 177 variables and pinned bytes.')
