"""Exact Sel_2 for the already-indexed scalar base β (not the new partner amplitude)."""
from math import prod,isqrt
import json
base=(-1,2,3,5,11,17,163,661,733,1489,1861)
beta=204618888056724185
def bits(v,p):
 a=0
 while v%p==0:v//=p;a^=1
 if p==2:return a|{1:0,3:6,5:4,7:2}[v%8]
 return a|2*(pow(v,(p-1)//2,p)==p-1)
def image(p):
 d=3 if p==2 else 2
 # Root evaluations, then ordinary points from the square condition.
 O={0}|{bits(v,p)|bits(w,p)<<d for v,w in [(-3,-beta),(beta,1),(-3*beta,-beta)]}
 for e in range(8):
  if len(O)==2**d:break
  for root in (0,beta,-3*beta):
   for i in range(-48,49):
    if i%p==0:continue
    x=root+i*p**e
    if x in (0,beta,-3*beta):continue
    u,v,w=[bits(t,p) for t in (x,x-beta,x+3*beta)]
    if not u^v^w: O.add(u|(v<<d))
 assert len(O)==2**d
 return O,d
def ker(rows,width):
 piv={}
 for r in rows:
  while r:
   j=r.bit_length()-1
   if j not in piv:piv[j]=r;break
   r^=piv[j]
 out=[]
 for i in range(width):
  if i in piv: continue
  v=1<<i
  for j,row in sorted(piv.items()):
   if (row&v).bit_count()%2:v^=1<<j
  assert all(not((row&v).bit_count()%2) for row in rows);out.append(v)
 return out
def main():
 assert prod(base[3:])==beta and all(all(p%a for a in range(2,isqrt(p)+1)) for p in base[1:])
 w=len(base);rows=[1|1<<w];local={}
 for p in base[1:]:
  O,d=image(p);cols=[bits(a,p) for a in base];cols +=[c<<d for c in cols]
  for h in range(1<<(2*d)):
   if all(not ((o&h).bit_count()%2) for o in O):
    rows.append(sum(((h&c).bit_count()%2)<<i for i,c in enumerate(cols)))
  local[p]=[sorted(O),len(ker(rows,2*w))]
 val=lambda mask:prod(a for i,a in enumerate(base) if mask>>i&1)
 basis=[[val(u),val(u>>w)] for u in ker(rows,2*w)]
 assert basis==[[-3,-beta],[8965,134909253259],[22824192755909,134909253259]]
 return dict(beta=beta,local_images_and_remaining_dim=local,basis=basis)
if __name__=='__main__':print(json.dumps(main(),sort_keys=True,indent=2))
