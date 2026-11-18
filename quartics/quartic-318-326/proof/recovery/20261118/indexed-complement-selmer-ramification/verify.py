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
 allp=primes()
 beta_primes=[5,11,17,163,661,733,1489,1861];B=prod(beta_primes)
 assert B==i.beta and set(beta_primes)<=allp
 hits=(61,109,6551,17377);original={}
 for p in map(int,i.data['annihilators']):
  z=i.probe(p,2 if p in hits else 1);assert z is not None
  original[p]=z
  assert (z['D']%p==0)==(p in hits)
  if p in hits:assert z['D']!=0
 out={}
 for k in (4,12):
  m=k*k*B; ram=set(beta_primes)
  fs=[{int(x):v for x,v in row.items()} for row in i.data['baseline_factors'][str(k)]]
  assert [prod(x**v for x,v in row.items()) for row in fs]==[m-1,25*m-9]
  rpr=sorted(ram|set(fs[0])|set(fs[1])|{2,3});assert set(rpr)|set(hits)<=allp
  base=[-1]+rpr;n=len(base);rows=[];steps=[]
  for p in rpr+list(hits):
   if p==7:continue
   th=1 if p in (2,3) or p in ram else original[p]['D']
   C=th*(1-m);r1=B*C*(25*m-9);r2=16*B*C*m
   O=local(p,r1,r2);d=3 if p==2 else 2
   cols=[loc(x,p) for x in base];cols += [c<<d for c in cols]
   for z in range(1,1<<(2*d)):
    if all((o&z).bit_count()%2==0 for o in O):
     rows.append(sum(((x&z).bit_count()%2)<<j for j,x in enumerate(cols)))
   steps.append([p,sorted(O),len(ker(rows,2*n))])
  # optional archimedean sign: x-r1>0 (or derivative squareclass at root).
  rows.append(1<<n)
  def val(w):return prod(a for j,a in enumerate(base) if (w>>j)&1)
  G=[[val(w),val(w>>n)] for w in ker(rows,2*n)]
  assert G==[[1,B]]
  out[k]=dict(fixed_generators=base,steps_prime_local_image_dimension=steps,final_basis=G)
 return dict(actual_residues=original,screens=out)
if __name__=='__main__':print(json.dumps(main(),indent=2))
