from find_pair import basis,setup
from engine import run,n
from functools import reduce
from operator import xor
from pathlib import Path
import numpy as np,json,itertools
def echelon(xs):
 d={}
 for x in xs:
  while x:
   j=x.bit_length()-1
   if j in d:x^=d[j]
   else:d[j]=x;break
 return d
def rem(x,d):
 for i in sorted(d,reverse=True):
  if x>>i&1:x^=d[i]
 return x
def encoder(G,H,N):
 m=(1<<N)-1;vs,gi=G;hs,hi=H;dim=gi-hi
 pivs=[np.flatnonzero(v)[0] for v in vs]
 def digit(vs1):
  x=vs1.copy();mask=0
  for i,(v,j) in enumerate(zip(vs,pivs)):
   a=int(x[j]);b=int(v[j]);assert a%b==0
   if a:
    r=a//b
    if r&1:mask|=1<<i
    x=(x-r*v)&m
  assert not np.any(x)
  return mask
 rels=[digit(v) for v in hs]+[digit((g*((1<<N)//int(g[j])))&m) for g,j in zip(vs,pivs)]
 d=echelon(rels)
 assert len(vs)-len(d)==dim
 return lambda v:rem(digit(v),d)
def record(q,N=4):
 tab,B,_=run(q,'finite',True);diag=[sum((int(f.get((0,),0))%2)<<j for j,f in enumerate(tab[i][i])) for i in range(n)]
 def sq(v):return reduce(xor,(z for i,z in enumerate(diag) if v>>i&1),0)
 fro=[sq(sq(sq(v))) for v in diag];assert len(echelon(fro))==1
 origin=sum(int(x!=0)<<i for i,x in enumerate(fro));roots,G=setup(q,N,origin);S=G[0][0];mask=(1<<N)-1
 h=[G[k][1]-G[k+1][1] for k in range(N)]
 enc=encoder(G[1],G[2],N)
 # compute coordinates of generators = multiplying ambient identity. In practice use entire R row image
 # modulo m² since residue F2 and exactly one rational character: image of each is <=1-dimensional.
 ro=[];coords=[]
 for i,M in enumerate(roots):
  z=echelon(enc(v) for v in ((S@M)&mask));assert len(z)<=1
  if not z:continue
  cv=next(iter(z.values()))
  if len(echelon(coords+[cv]))>len(coords):coords.append(cv);ro.append(i)
 assert len(ro)==h[1]
 combs=sorted(range(1,1<<len(ro)),key=lambda i:(i.bit_count(),i))
 for k in range(1,N-1):
  cod=encoder(G[k+1],G[k+2],N);dom=G[k][0]
  genmaps=[[cod(v) for v in ((dom@roots[i])&mask)] for i in ro]
  maps={0:[0]*len(dom)};images={}
  for c in range(1,1<<len(ro)):
   j=c.bit_length()-1;maps[c]=[a^b for a,b in zip(maps[c^(1<<j)],genmaps[j])]
   images[c]=list(echelon(maps[c]).values())
  target=h[k+1];found=None
  for a,b in itertools.combinations(combs,2):
   if len(images[a])+len(images[b])>=target and len(echelon(images[a]+images[b]))==target:
    found=(a,b);break
  if found:
   def mfun(x):return sum(roots[i] for j,i in enumerate(ro) if (x>>j)&1)&mask
   fs,gs=map(mfun,found);src=G[k][0]
   test=basis(np.vstack((G[k+2][0],src@fs,src@gs)),N)[1]
   assert test==G[k+1][1]
   jsize=basis(np.vstack((S@fs,S@gs)),N)[1]
   return {'q':list(q),'origin':origin,'N':N,'hilbert':h,'cotangent':ro,'masks':found,'k':k,'multiplicity':G[0][1]-jsize,'strict_cardinality_check':[test,G[k+1][1]]}
 return {'q':list(q),'origin':origin,'N':N,'hilbert':h,'cotangent':ro,'masks':None}
if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 qs=[q for q in itertools.product((1,-1,2,-2),repeat=4) if len(set(q[:3]))>1]
 with ProcessPoolExecutor(max_workers=2) as ex:
  out=[]
  for i,v in enumerate(ex.map(record,qs),1):
   out.append(v)
   if i%24==0:print(i,sum(x['masks'] is not None for x in out),flush=True)
 Path(__file__).with_name('candidates.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
