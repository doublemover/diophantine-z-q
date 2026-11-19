from collections import Counter
from pathlib import Path
from fractions import Fraction as Q
import json
def read(p,k=0):
 C=json.loads((P/(p+'TRANSFER.json')).read_bytes());r=json.loads((P/(p+'QUADRICS.json')).read_bytes())['rows'];inv={i:int(x) for x,i in C['renumber'].items()};by={};rows=[]
 for row in r:
  eq=Counter()
  if row['name']=='u*uInv':
   assert len(row['terms'])==2 and {tuple(inv[i] for i in t['monomial'])for t in row['terms']}=={(),(900,901)} and {t['coefficient']for t in row['terms']}=={'1','-1'}
   continue
  for t in row['terms']:
   x=[inv[z] for z in t['monomial']];vs=[i for i in x if i not in (900,901)];e=x.count(900)-x.count(901)-sum(C['weights'].get('x%d_0'%i,0) for i in vs)
   if k:vs=[i+100 if i in (*range(410,418),420,421) else i for i in vs]
   eq[e,t['parameterPower'],tuple(sorted(vs))]+=int(t['coefficient'])
  eq={i:v for i,v in eq.items() if v};m=min(eq);can=tuple(sorted(((a-m[0],b,vs),Q(v,eq[m])) for (a,b,vs),v in eq.items()));rows.append((row['name'],can))
 return rows
import sys
P=Path(__file__).resolve().parent
assert len(sys.argv)==3,'python ROW-REVIEW.py <189 symbolic folder> <170 symbolic folder>'
target=read('');P=Path(sys.argv[1]);old=read('',True);P=Path(sys.argv[2]);mix=read('')
discard=('new.det0.factor','amplified.det0.product','amplified.C1.power4','cleared.E1.square','cleared.E2.square','cleared.E3.square','cleared.E4.square','homogeneous.H.square','input.cleared.square','input.cleared.fourth')
expected=Counter(z for z in old if not z[0].startswith(discard));expected.update(z for z in mix if z[0].startswith(('rebuilt.factor.','chain')));assert Counter(target)==expected;print(len(target),'nonunit rows compose exactly')
