from fractions import Fraction as F
from math import prod
from pathlib import Path
from hashlib import sha256
import json, sys
def read_pin(arg,sha):
 b=Path(arg).read_bytes()
 assert sha256(b).hexdigest()==sha
 return json.loads(b)
def jacobi(a,b):
 assert b>0 and b%2
 a%=b;s=1
 while a:
  while a%2==0:
   a//=2
   if b%8 in (3,5):s=-s
  a,b=b,a
  if a%4==b%4==3:s=-s
  a%=b
 return s if b==1 else 0
def mod(x,p):return x.numerator*pow(x.denominator,-1,p)%p
T=read_pin(sys.argv[1],'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec')
S=read_pin(sys.argv[2],'d8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0')
C=read_pin(sys.argv[3],'de9065dd38ae14d076507e6a307da281e6e51da62b7ad86fe6db10cb3eac3111')
theta={1:F(-1,2),2:F(-1),3:F(1,2399),4:F(-32,407)}
for name,records,L in [('triad', T['rows'],(7,7,7)), ('six',T['rows']+S['rows'],(23,19,19))]:
 W={}; k2=[prod(row['prime'] for row in records if row['assigned_scale']==j) for j in range(3)]
 for row,claimed in zip(records,C[name]['local_symbol_rows'],strict=True):
  p=row['prime'];k=row['assigned_scale'];z=F(row['r_over_d_mod_p2']); cs=row['scales_mod_p2']
  assert [k,2]==claimed['hit'] and p==claimed['prime']
  slots=set()
  for j,i,m,sgn,unk in claimed['rows']:
   slots.add(mod(theta[i]/cs[j]**2,p))
   y=(cs[j]*z)**2-theta[i]
   hit=(j,i)==(k,2)
   assert mod(y,p*p)==p if hit else bool(mod(y,p))
   v=mod(y/(p if hit else 1),p)
   assert v==m%p and jacobi(v,p)==sgn
   known=k2[j] if i==2 else 1
   if hit:known//=p
   assert jacobi(v*known,p)==unk
   if i!=2 and sgn<0:W.setdefault((j,i),p)
  assert len(slots)==12 and 0 not in slots
 assert [(*k,W[k]) for k in sorted(W)]==[tuple(x) for x in C[name]['forced_unhit_classes']]
 assert len(W)==9 and [jacobi(k,l) for k,l in zip(k2,L)]==[-1]*3
 low=len(records)+3+len(W)
 assert low==C[name]['total_support_lower_bound']
 print(name, 'classes',sorted(W.items()), 'total lower',low)
