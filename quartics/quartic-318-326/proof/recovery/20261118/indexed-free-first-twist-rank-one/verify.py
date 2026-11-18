import json
from math import gcd
from math import prod
import original_probe as i
def loc(a,p):
 v=0
 while a%p==0:a//=p;v^=1
 if p==2:return v|{1:0,3:6,5:4,7:2}[a%8]
 return v|(2 if pow(int(a%p),(p-1)//2,p)==p-1 else 0)
def local(p,r,s):
 d=3 if p==2 else 2
 out={0};needed=8 if p==2 else 4
 for x,y in [(r*s,-r),(r,r*(r-s)),(s,s-r)]:out.add(loc(x,p)|(loc(y,p)<<d))
 for e in range(8):
  if len(out)==needed:break
  for start in (0,r,s):
   for a in range(-48,49):
    if not a%p:continue
    x=start+a*p**e
    if x in (0,r,s):continue
    l,m,n=loc(x,p),loc(x-r,p),loc(x-s,p)
    if l^m^n==0:out.add(l|(m<<d))
 assert len(out)==needed,(p,out)
 return out
def ker(rows,n):
 piv={}
 for r in rows:
  while r and r.bit_length()-1 in piv:r^=piv[r.bit_length()-1]
  if r:piv[r.bit_length()-1]=r
 out=[]
 for j in range(n):
  if j in piv:continue
  w=1<<j
  for a in sorted(piv):
   if (piv[a]&w).bit_count()%2:w|=1<<a
  out.append(w)
 return out
def primes():
 proof=i.data['primality']
 for p in sorted(map(int,proof)):
  g,f=proof[str(p)]
  if p==2:continue
  assert all(q<p and str(q) in proof and v>0 for q,v in f)
  assert p-1==prod(q**v for q,v in f) and pow(g,p-1,p)==1
  assert all(gcd(pow(g,(p-1)//q,p)-1,p)==1 for q,v in f)
 return set(map(int,proof))
def main():
 primes_ = primes();b=i.beta;t=18;m=b*t*t
 assert b%24==17
 fs=[{int(x):v for x,v in row.items()} for row in i.data['factors']]
 assert [prod(p**v for p,v in row.items()) for row in fs]==[b,m-1,9*m-1]
 f1=set(fs[0]);fp=set().union(*(set(row) for row in fs));assert fp<=primes_
 n=prod(p for p in fp if sum(r.get(p,0) for r in fs)%2)
 assert n==b*(1-m)*(1-9*m) and n%24==17
 X=b*(1+3*m)**2;Y=8*b*b*t*(1+3*m)*(1-3*m)
 assert Y*Y==X*(X-n)*(X+3*n) and Y and X-n==(4*b*t)**2 and X+3*n==b*(2*(1-3*m))**2
 hits={61,109,6551,17377}
 ds={p:i.probe(p,2 if p in hits else 1) for p in map(int,i.data['annihilators'])}
 assert all(ds.values()) and all(z['D'] for z in ds.values())
 assert all(ds[p]['D']%p==0 for p in hits)
 assert all(z['D']%p!=0 for p,z in ds.items() if p not in hits)
 # 7-adic input: opposite smooth branch cusp and other formal, cf. matching-root-signs source.
 assert i.h%7==i.m%7==3 and i.h%8==0 and (i.m//i.h)%7==1
 N=(1+2*pow(i.r,-1,7))%7;q2=pow(i.r,-30,7);W=(N*N+i.r*q2)%7
 d7=(1-i.A*W**2*pow(17*(1+i.A)**2,-1,7))%7;assert d7==6
 base=[-1]+sorted({2,3}|fp);l=len(base);ans={}
 for partner in (False,True):
  rows=[1|(1<<l)];table=[]
  for p in sorted(set(base[1:])|(hits if partner else set())):
   th=1 if not partner or p in [2,3] or p in f1 else d7 if p==7 else ds[p]['D']
   a=n*th
   while a%p**2==0:a//=p*p
   O=local(p,a,-3*a);d=3 if p==2 else 2
   cols=[loc(z,p) for z in base];cols +=[w<<d for w in cols]
   for z in range(1,1<<(2*d)):
    if all((z&o).bit_count()%2==0 for o in O):rows.append(sum(((z&w).bit_count()%2)<<j for j,w in enumerate(cols)))
   table.append([p,sorted(O),len(ker(rows,2*l))])
  def val(w):return prod(a for j,a in enumerate(base) if w>>j&1)
  K=[[val(w),val(w>>l)] for w in ker(rows,2*l)]
  assert K==([[b,1]] if partner else [[-3,-n],[b,1],[n//b,1]])
  ans['partner' if partner else 'first']=dict(table=table,basis=K)
 return dict(t=t,beta=b,squarefree_amplitude=n,first_point=[X,Y],D7=d7,original_residues=ds,screens=ans)
if __name__=='__main__':print(json.dumps(main(),indent=2))
