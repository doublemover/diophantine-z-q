"""Privately compile a finite-coefficient 180-variable chart with a recycled slot."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
from math import gcd,lcm,prod
from functools import reduce
import json,hashlib,runpy,sys
P=Path(__file__).resolve().parent;S=P.parent/'effective180';dst=P/'proposal'
g=runpy.run_path(str(S/'verify.py'));tbl=dict(g['fixed']);xw,rw=g['xw'],g['rw'];C=149**15;L=557*149**2
def rk(es):return g['norm']((e,c,tuple(m),F(v))for e,c,m,v in es)
oldnames=('scalar.W2.definition','scalar.b.definition','parity_scalar.reduced_scalar.root.power4','unsaturated.scalar')
assert 104 in {i for rr in tbl.values()for e,c,m in rr for i in m}
assert {n for n,rr in tbl.items()if any(104 in m for e,c,m in rr)}==set(oldnames[:2])
# In situ spelling preserves order exactly. The previous row-weight for each newly named row is explicitly set.
new0=rk([((0,0),0,(111,111),1),((0,0),0,(105,113),-1)])
new1=rk([((0,1),0,(104,),1),((0,0),0,(104,),F(705023,51)-48),((0,0),0,(),-1)])
new2=dict(tbl[oldnames[2]]);assert new2.pop(((0,0),1,(109,112)))==1;new2[((1,0),0,(109,))]=1
# P polynomial in s. Compute A-P at a0 by exact Taylor expansion about a0, not trusting 181 metadata.
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return r
poly=mul(mul([1,-51],[-2400,-51]),[375,-1632]);a0=F(-705023,51)
A=sum(c*a0**i for i,c in enumerate(poly));assert A==11176009070309724672
b=-poly[3];c=-poly[2]-2*a0*poly[3];d=-(poly[1]+2*a0*poly[2]+3*a0*a0*poly[3])
assert all(sum(co*F(i)**j for j,co in enumerate(poly))+(F(i)-a0)**2*(b*i+c)+(F(i)-a0)*d==A for i in [-1,0,1,2])
u=[((0,1),0,(),b),((0,0),0,(),c-48*b),((0,0),0,(104,),d)]
new3=rk(u+[((-1,h),-1,tuple(m)+(113,),-F(149,L)*v) for ((j,h),cp,m,v)in u]+[((0,0),0,(104,104),-A)])
xw[104]=(0,0);rs=[new0,new1,new2,new3];ns=['scalar.cubicPole','saturated.scalar.interpolationInverse','scalar.reweightedOddComponent','saturated.scalar.denominator'];weights=[(2,0),(0,0),(2,0),(0,0)]
rep=dict(zip(oldnames,zip(ns,rs,weights)));fixed={}
for n,rr in tbl.items():
 if n in rep:
  n,rr,w=rep[n];rw[n]=w
 fixed[n]=rr
# Graph checker requires every Laurent monomial use no more than two actual slots, including residual harmonic q replacement.
Q,ren=g['graph'](fixed,[314,334,714]);assert Q['variables']==180 and len(Q['rows'])==152 and g['xw'][1]==(0,0)
out=[]
for r in Q['rows']:
 d=Counter()
 for t in r['terms']:d[tuple(t['monomial'])]+=int(t['coefficient'])*C**t['parameterPower']
 G=gcd(*d.values());assert G>0
 out.append(dict(id=r['id'],name=r['name'],terms=[[m,v//G]for m,v in sorted(d.items())if v]))
def write(n,x):(dst/n).write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')
write('QUADRICS.json',out)
write('TRANSFER.json',dict(renumber=ren,scalar_inverse_old_id=104,center=str(a0),L=L,A=int(A),C=str(C),integer_N=15,effective_point_label='X^2+48',gauges={i:xw[i] for i in xw if i in ren},rowWeights={n:rw[n]for n in fixed}))
def expand(out):
 pol=Counter()
 for r in out:
  assert all(len(m)<=2 for m,v in r['terms'])
  for (m,v),(k,a)in product(r['terms'],repeat=2):pol[tuple(sorted(tuple(m)+tuple(k)))]+=v*a
 p={m:b for m,b in sorted(pol.items())if b};assert p[(1,1,1,1)]==1 and {x for m in p for x in m}==set(range(1,181))
 write('POLYNOMIAL.json',list(p.items()));form=''
 for m,v in p.items():
  z=['x%d'%i+('^%d'%k if k!=1 else '') for i,k in sorted(Counter(m).items())]
  if abs(v)!=1 or not z:z.insert(0,str(abs(v)))
  form+=('-'if v<0 else '+'if form else '')+'*'.join(z)
 (dst/'quartic180-N15.txt').write_text(form);print(len(out),len(p),max(abs(v).bit_length()for v in p.values()),len(form),hashlib.sha256(form.encode()).hexdigest())
expand(out)
