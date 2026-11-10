#!/usr/bin/env python3
import itertools,json
from fractions import Fraction as F
import mpmath as m
import sympy as s
m.mp.dps=80
counts=dict(adjacent_equivalences=0,original_source_covers=0,nonzero_multiple_counts=0,finite_divisor_counts=0,full_box_counts=0,weighted_source_bounds=0,same_pattern_injections=0,complete_position_unions=0,growing_cutoff_bounds=0,exact_exponents=0)
def le(a,b):assert a<=b*(1+m.mpf('1e-65'))+m.mpf('1e-65'),(a,b)
def norm(a,b,sg):return (a+sg)**2+b*b
for p,a,b in itertools.product(list(s.primerange(3,60)),range(-20,21),range(-20,21)):
 assert (norm(a,b,1)%p==norm(a,b,-1)%p==0)==(a%p==0 and (b*b+1)%p==0)
 counts['adjacent_equivalences']+=1

def weight(a,b,w,gs):return m.fprod(m.log(max(1,abs(a*a+b*b+g*w*w))) for g in gs)
def pw(uw,cs):u,w=uw;return m.fprod(m.log(max(1,abs(u+c*w*w))) for c in cs)
def bad(a,b,Y):return [p for p in s.factorint(b*b+1) if p>Y and a%p==0]
for B,Y in itertools.product(range(1,10),[2,3,5,11,31,101]):
 vals=range(-B,B+1);source=[v for v in itertools.product(vals,repeat=3) if bad(v[0],v[1],Y)]
 image=[];target=0
 for a,b,w in source:
  if a==0:tag=('zero',b,w)
  else:
   p=bad(a,b,Y)[0];tag=('nonzero',b,p,a,w)
   assert p in s.divisors(b*b+1) and p>Y and a%p==0 and a!=0
  image.append(tag)
 assert len(set(image))==len(source);counts['original_source_covers']+=len(source)
 target=(2*B+1)**2
 for b in vals:
  ps=[p for p in s.factorint(b*b+1) if p>Y]
  assert len(ps)<=len(s.divisors(b*b+1));counts['finite_divisor_counts']+=1
  for p in ps:
   aa=[a for a in vals if a!=0 and a%p==0]
   assert len(aa)==2*(B//p) and len(aa)<=m.mpf(2*B)/Y
   counts['nonzero_multiple_counts']+=1
   target+=len(aa)*(2*B+1)
 assert len(source)<=target;counts['full_box_counts']+=1
 for d in [m.mpf('.001'),m.mpf('.25'),m.mpf(1)]:
  D=m.mpf(100) # explicit overestimate of all actual finite tau(n)/n^d in this test range
  assert all(len(s.divisors(b*b+1))<=D*(b*b+1)**d for b in vals)
  budget=(2*B+1)**2*(1+m.mpf(2*B)/Y*D*(B*B+1)**d)
  le(target,budget);counts['finite_divisor_counts']+=1
  growth=9*m.mpf(B)**2+18*D*2**d*m.mpf(B)**(3+2*d)/Y
  le(budget,growth);counts['full_box_counts']+=1
 for gs in [[],[0],[-2,0,1]]:
  W=m.fprod(m.log((2+abs(g))*B*B) for g in gs)
  le(sum(weight(a,b,w,gs) for a,b,w in source),len(source)*W);counts['weighted_source_bounds']+=1
 for ci in [-3,0,2]:
  pat={}
  for v in source:
   a,b,w=v;uw=(a*a+b*b-ci*w*w,w);pat.setdefault(uw,v)
  assert len(set(pat.values()))==len(pat)
  for cs in [[],[ci],[ci,ci+2]]:
   for uw,(a,b,w) in pat.items():assert all(uw[0]+c*w*w==a*a+b*b+(c-ci)*w*w for c in cs)
   le(sum(pw(uw,cs) for uw in pat),sum(weight(a,b,w,[c-ci for c in cs]) for a,b,w in source))
   counts['same_pattern_injections']+=len(pat)
for B,cs in itertools.product([1,2,3],[[],[0],[0,1],[-2,0,3]]):
 vals=range(-B,B+1);pairs=list(itertools.permutations(range(len(cs)),2))
 Y=max([3]+[abs(cs[i]-cs[j]) for i,j in pairs]+[int(m.ceil(m.mpf(B)**m.mpf('.01')))])
 same={};dist={};sm=m.mpf(0);dm=m.mpf(0)
 for i,ci in enumerate(cs):
  local=set()
  for a,b,w in itertools.product(vals,repeat=3):
   if bad(a,b,Y):local.add((a*a+b*b-ci*w*w,w))
  sm+=sum(pw(z,cs) for z in local)
  for z in local:same.setdefault(z,('same',i,z))
 for i,j in pairs:
  local=set();k=cs[i]-cs[j]
  for a,b,c,d,w in itertools.product(vals,repeat=5):
   if a*a+b*b-c*c-d*d!=k*w*w:continue
   for sa,sc in itertools.product([1,-1],repeat=2):
    G=norm(a,b,sa);H=norm(c,d,sc)
    if G==H==0 or any(p>Y for p in s.factorint(s.gcd(G,H))):
     local.add((a*a+b*b-cs[i]*w*w,w));break
  dm+=sum(pw(z,cs) for z in local)
  for z in local:dist.setdefault(z,('distinct',i,j,z))
 union=dict(same);union.update(dist)
 assert len(set(union.values()))==len(union)
 le(sum(pw(z,cs) for z in union),sm+dm);counts['complete_position_unions']+=1
for bi,gs in itertools.product([1,2,10,10**6,10**30,10**100],[[],[0],[-3,0,2],[1,-1,3,9]]):
 B=m.mpf(bi);d=m.mpf('.001');e=d;eta=e/(len(gs)+1);D=m.mpf(100)
 C=m.fprod(m.log(2+abs(g))+2/eta for g in gs)
 W=m.fprod(m.log((2+abs(g))*B**2) for g in gs)
 Y=max(3,m.ceil(B**m.mpf('.01')))
 budget=(2*B+1)**2*(1+2*B/Y*D*(B**2+1)**d)
 final=(9+18*D*2**d)*C*B**(3-m.mpf(1)/200)
 le(W*budget,final);counts['growing_cutoff_bounds']+=1
assert F(2)+F(1,1000)<=3-F(1,200)
assert F(3)+3*F(1,1000)-F(1,100)<=3-F(1,200)
counts['exact_exponents']=2
print(json.dumps({'status':'PASS','precision_digits':80,'checks':counts,'scope':'Actual same-position source, zero coordinate, finite divisor consumers and complete original pattern cover; not prime existence.'},sort_keys=True))
