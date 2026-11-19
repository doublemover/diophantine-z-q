"""Independent physical-source, weighted-subset, height-budget and literal recheck; Python stdlib."""
from pathlib import Path
from itertools import product,combinations
from collections import Counter
from fractions import Fraction as F
from math import gcd,prod
import json,sys,hashlib,re
new,old=map(Path,sys.argv[1:3]);rd=lambda p,n:json.loads((p/n).read_bytes());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(old/'QUADRICS.json')=='df3ecc34963e714f393a744a47bf4483c265da9ea228aaed8c7f74c3bdf59c79'
data=rd(new,'ROW-MAP.json');ren={int(k):v for k,v in data['new_index'].items()};back={v:k for k,v in ren.items()};assert set(ren)==set(range(1,181))-{164,165}and list(sorted(back))==list(range(1,179)) and ren[1]==1
oldT=rd(old,'TRANSFER.json');orig={int(v):int(k)for k,v in oldT['renumber'].items()}
def row(r,mapping):return {tuple(sorted(mapping[i]for i in m)):c for m,c in r['terms']}
orig_rows=rd(old,'QUADRICS.json');O=[row(r,{i:i for i in range(1,181)})for r in orig_rows];new_rows=rd(new,'QUADRICS.json');N=[row(r,back)for r in new_rows]
assert all(set(r)=={m for m in r if 164 not in m and 165 not in m} for i,r in enumerate(O,1)if i not in(78,137,138,139))
P=lambda d:{tuple(sorted(orig[i]for i in m)):v for m,v in d.items()}
def field(a,b): # (A+ρB)(C+ρD)
 r,i={},{}
 for a,c,fac,where in[(a[0],b[0],1,r),(a[1],b[1],2,r),(a[0],b[1],1,i),(a[1],b[0],1,i)]:
  for k,v in a.items():
   for l,w in c.items():
    m=tuple(sorted(k+l));where[m]=where.get(m,0)+fac*v*w
 return r,i
def scalar(ii):return {(ii,):1}
def plus(*rs):
 ret=Counter()
 for r in rs:ret.update(r)
 return {m:z for m,z in ret.items()if z}
cx=lambda i:tuple(scalar(i+j)for j in(0,1))
# Recover z*h1=hscaled x209,210 and z(s1+t1) components. The conjugated opposite mark changes sign on x32 only.
h=cx(209);B=({(17,):1,(29,):-1,(150,):1,(31,):-1},{(18,):1,(30,):-1,(151,):1,(32,):1})
first=field(h,[plus(a,b)for a,b in zip(h,B)])
for j in (0,1):
 assert P(O[[136,138][j]])==plus(first[j],{(101,605+j):-1})
other=[]
for base in (213,225):
 g=cx(base+8);ss=cx(base);tt=cx(base+2);other.append(field(g,[plus(a,b,c)for a,b,c in zip(g,ss,tt)]))
constant=[{():26,(2,):2,(86,):-2,(192,):1},{():-8,(2,):2,(86,):-4,(700,):2,(193,):1}]
args=[plus(constant[j],*(a[j] for a in other))for j in (0,1)]
assert P(O[77])==plus(args[0],{(605,):1}) and P(O[137])==plus(args[1],{(606,):1})
assert P(O[0])=={():48,(1,1):1,(45,):-1} and P(O[151])=={(45,45):1,(101,):-1}
ii=0
for i,o in enumerate(O,1):
 if i in (137,139):continue
 n=N[ii];assert new_rows[ii]['id']==ii+1;ii+=1
 if i in(78,138):j=0 if i==78 else 1;assert P(n)==plus(first[j],args[j])
 else:assert o==n
assert ii==150 and len(N)==ii
# Exhaust every principal subset (torsion-zero indices can only be omitted), compare to the common formal log with denominators.
indices=[-7,11,-13,17]
for i in range(4):
 subsets=[J for n in range(1,5)for J in combinations(range(4),n)if i in J]
 assert len(subsets)==8 and sum(2*(len(J)-1)for J in subsets)==24 and prod(len(J)for J in subsets)==864
 for a,b in [(48,1),(49,1),(193,4),(433,9)]:
  weights=[a*a,b*b,b*b,b*b];mx=max(a,b)
  for J in subsets:
   C=sum(weights[j]*prod(indices[k]**2 for k in J if k!=j)for j in J)
   assert C>0 and C<=mx**2*len(J)*max(map(abs,indices))**(2*(len(J)-1))
   assert F(C,prod(indices[k]**2 for k in J if k!=i))==indices[i]**2*sum(F(weights[j],indices[j]**2)for j in J)
# Exact height comparisons and scalings, including Δ nonzero endpoints. 720 h(z)+2500<361B, B>=149^66.
assert 149**66>361000 and 149**66>2500 and 2**240*(43*67*191*557*702623)**3<149**66
# 121 sqrt(21/10)*14^(1/3+1/36036) < 121*(29/20)*(5/2) < 450. Thus harmless even after moving B/1000.
assert F(29,20)**2>F(21,10) and 14**12013*2**36036<5**36036
assert 121*F(29,20)*F(5,2)*F(1000,999)<500
# Parse the actual ASCII coefficient record through formal expansion.
p4=Counter()
for r in new_rows:
 assert gcd(*(c for m,c in r['terms']))==1
 for(m,a),(n,b)in product(r['terms'],repeat=2):
  assert len(m)<=2;p4[tuple(sorted(m+n))]+=a*b
p4={m:c for m,c in p4.items()if c};assert p4=={tuple(m):c for m,c in rd(new,'POLYNOMIAL.json')}
raw=(new/'quartic178-N15.txt').read_text();terms=re.findall(r'[+-]?[^+-]+',raw);assert ''.join(terms)==raw;got={}
for term in terms:
 t=term.lstrip('+-').split('*');sgn=-1 if term[0]=='-'else 1
 c=sgn*(int(t.pop(0))if t and t[0][0].isdigit()else 1);m=[]
 for v in t:
  mm=re.fullmatch(r'x([1-9][0-9]*)(?:\^([2-4]))?',v);assert mm
  m.extend([int(mm.group(1))]*int(mm.group(2)or 1))
 m=tuple(sorted(m));assert m not in got;got[m]=c
assert len(new_rows)==150 and p4==got and {i for m in p4 for i in m}==set(range(1,179)) and p4[(1,)*4]==1
assert (len(raw),len(p4),max(abs(c).bit_length()for c in p4.values()))==(87020,3494,365) and H(new/'quartic178-N15.txt')=='2dbf9ae700ad51104ddd8cd9af3d1436fb768f17c3def61cf834fffe0769a96f'
print('PASS precise four true weighted abscissas; 148 exact untouched residuals + 2 new; all 8-subset and numerical controls; strict literal 178/150/3494/365.')
# Author's sharper separation of overhead: refresh independently for both Δ cases.
assert 149**66>10**9 and F(400000,9999)*3<F(12002,100) and F(12002,100)*10000/9999<121 and 4*F(12002,100)<484
# ||C_t||_1 ≤16.75 by |sqrt2|<3/2; affine intercept |−26+8ρ|+(1+3)|d|+1≤57.
assert (2+2*F(3,2))+(2+4*F(3,2))+2*F(3,2)+26+8*F(3,2)+4*F(9,2)+1<100
