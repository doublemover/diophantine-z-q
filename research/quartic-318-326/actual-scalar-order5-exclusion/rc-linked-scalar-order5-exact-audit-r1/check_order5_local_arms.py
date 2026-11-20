"""Recompute only the three exact survivors from the fixed scalar donor."""
from pathlib import Path
from contextlib import redirect_stdout
from math import isqrt
import runpy,io,json
with redirect_stdout(io.StringIO()):
 s=runpy.run_path(str(Path(__file__).resolve().parent.parent/
 'rc-linked-scalar-specialization-r1/select_scalar_specialization.py'))
h=s['h']; k=s['shift']; R=s['R']; B=s['B']; M=s['A']+1
assert h==473592745039516333133760
assert k%(5*h)==0 and s['vp'](k//h,5)==8
out=[]
for p in (521,89,199):
 assert all(p%q for q in range(2,isqrt(p)+1))
 places=s['places'](p);assert len(places)==2
 points=[];vals=[];orders=[]
 for e in places:
  n=e.order();orders.append(n)
  assert e.nsmul(k%n) is None
  Q=e.nsmul(h%n);points.append(Q)
  if Q is None:vals.append(0)
  else:
   assert e.nsmul(5,Q) is None
   x,y=Q
   assert y and (x*x+e.D)%p
   vals.append(2*y*pow(x*x+e.D,-1,p)%p)
 assert sum(v!=0 for v in vals)==1
 N=(1+vals[0]**2*pow(R,-1,p))*(1+vals[1]**2*pow(R,-1,p))%p
 W=N*N%p
 c=12*W*pow(M,-1,p)%p
 D=B*c*c%p
 F=(49*D-48)%p
 assert (D!=1 if p==521 else F!=0)
 out.append(dict(p=p,roots=[e.d for e in places],orders=orders,retained_h_ordinates=points,
       U=vals,W=W,c=c,D=D,F=F))
print(json.dumps(out,indent=2))
