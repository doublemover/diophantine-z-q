"""Evaluate the closed characters, residue degrees and mixed cotangent dimensions of a point fibre."""
from functools import lru_cache
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'basis'))
from engine import run,n
def indices(x):
 while x:
  v=x&-x;yield v.bit_length()-1;x^=v
def xr(xs):
 v=0
 for x in xs:v^=x
 return v
def pivots(cols):
 b={}
 for x in cols:
  while x:
   i=x.bit_length()-1
   if i in b:x^=b[i]
   else:b[i]=x;break
 return b
def lin_solve(equations):
 # Rows have low n variables, nth high bit RHS. RREF high pivots, then solve ascending.
 B={}
 for r in equations:
  x=r&65535;rhs=r>>16
  while x:
   k=x.bit_length()-1
   if k in B:
    y,z=B[k];x^=y;rhs^=z
   else:B[k]=(x,rhs);break
  if not x:assert rhs==0
 def back(v,homog):
  for k,(r,b) in sorted(B.items()):
   if ((r&v).bit_count()&1)^(b if not homog else 0):v|=1<<k
  return v
 return back(0,False),[back(1<<j,True) for j in range(n) if j not in B]
def fibre(T,t0):
 def at(f):return int(f.get((0,),0)) if t0==0 else int(sum(f.values()))
 def der(f):return int(f.get((1,),0))%2 if t0==0 else int(sum(v for (k,),v in f.items() if k%2))%2
 ci=[[[at(f) for f in vec] for vec in row] for row in T]
 di=[[[der(f) for f in vec] for vec in row] for row in T]
 mult=[[sum((c&1)<<k for k,c in enumerate(vec)) for vec in row] for row in ci]
 @lru_cache(None)
 def mul(x,y):return xr(mult[i][j] for i in indices(x) for j in indices(y))
 @lru_cache(None)
 def sq(x):return xr(mult[i][i] for i in indices(x))
 equations=[sum(((mult[i][j]>>k)&1)<<i for i in range(n))|((j==k)<<n) for j in range(n) for k in range(n)]
 one,ker=lin_solve(equations);assert not ker and one
 fix=[sum((((mult[i][i]^(1<<i))>>k)&1)<<i for i in range(n)) for k in range(n)]
 _,idems=lin_solve(fix);parts=[one]
 for e in idems:
  ps=[]
  for a in parts:
   b=mul(a,e);c=a^b
   ps.extend(z for z in (b,c) if z)
  parts=ps
 red=[1<<i for i in range(n)]
 for _ in range(4):red=list(map(sq,red))
 parts=sorted(parts);result=[]
 for e in parts:
  r=len(pivots(mul(e,v) for v in red))
  assert r>0 and mul(e,e)==e
  v=[mul(e,1<<j) for j in range(n)]
  for _ in range(((4+r-1)//r)*r):v=list(map(sq,v))
  assert len(pivots(v))==r and all(mul(e,x)==x for x in v)
  def ev(bits):return xr(v[i] for i in indices(bits))
  assert all(mul(v[i],v[j])==ev(mult[i][j]) for i in range(n) for j in range(i,n))
  @lru_cache(None)
  def inv(x):
   assert x;out=e;p=(1<<r)-2;y=x
   while p:
    if p&1:out=mul(out,y)
    y=sq(y);p>>=1
   assert mul(x,out)==e
   return out
  rows={}
  for i in range(n):
   for j in range(i,n):
    c=ci[i][j]
    cumul=mul(v[i],v[j]);delt=0
    for a,x in zip(c,v):
     if ((-a-a*a)//2)&1:delt^=sq(x)
     if a&1:delt^=mul(cumul,x);cumul^=x
    assert not cumul
    dt=xr(x for x,a in zip(v,di[i][j]) if a)
    dy=[(e if a&1 else 0) for a in c];dy[i]^=v[j];dy[j]^=v[i]
    row=[delt,sq(dt)]+[sq(x) for x in dy]
    for k in range(18):
     c0=row[k]
     if not c0:continue
     if k in rows:
      row=[a^mul(c0,b) for a,b in zip(row,rows[k])]
     else:
      z=inv(c0);rows[k]=[mul(z,a) for a in row];break
  result.append({'idempotent_mask':e,'residue_degree':r,'embedding_dimension':18-len(rows)})
 assert sum(x['residue_degree'] for x in result)==len(pivots(red))
 return result
def calculate(q):
 d=lambda x:int(x<0)|2*int(abs(x)==2);cl=[d(i) for i in q]
 subgroup={0,cl[0]^cl[1],cl[0]^cl[2],cl[1]^cl[2]}
 assert subgroup!={0}
 p0=abs(q[0])==2;p3=abs(q[3])==2
 T,_,_=run(q,'finite',True)
 res={'q':list(q),'T=0':fibre(T,0)}
 if subgroup=={0,1} and p3:
  if p0:
   U,_,_=run(q,'reciprocal',True);res['infinity']=fibre(U,0)
  else:res['T=1']=fibre(T,1)
 return res
if __name__=='__main__':
 from itertools import product
 from concurrent.futures import ProcessPoolExecutor
 import json
 qs=[q for q in product((1,-1,2,-2),repeat=4) if len(set(q[:3]))>1]
 with ProcessPoolExecutor(max_workers=2) as ex:
  out=[]
  for j,a in enumerate(ex.map(calculate,qs),1):
   out.append(a)
   if j%24==0:print(j,flush=True)
 Path(__file__).with_name('initial-points-240.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
