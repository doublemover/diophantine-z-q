import json
from math import gcd,isqrt
import j7_eta
import j7_index7
import j1728_eta

p=19
assert pow(2,9,19)==18
u=(5,13); A=j7_eta
assert A.su(A.mu(A.z(2),A.di(A.z(1),u)),A.z(1))==(0,5)
assert 3*3*2%19==18
assert 1728*4*pow(4+27*13,-1,19)%19==7
assert (10*(-1)**3*5+8*5**3)%19==0

samples={}
for n in (47,119):
 assert n%24==23 and pow(-n%19,9,19)==18
 s0=next(s for s in range(1,19) if (7*s*s-n)%19==0)
 r0=5*s0*pow(3,-1,19)%19
 assert r0*r0%19==n%19
 p7=[];p1728=[]
 for U in range(-isqrt(7*n),isqrt(7*n)+1):
  if U%2!=1 or U%19!=7*s0%19:continue
  bnd=isqrt((7*n-U*U)//19)
  for V in range(-bnd,bnd+1):
   if (2*U+V)%7:continue
   q=7*n-U*U-19*V*V
   if q%133:continue
   W=isqrt(q//133)
   if W*W*133!=q:continue
   w=(2*U+V)//7-2
   for c in sorted({-W,W}):
    if (c-w)%2:continue
    x=(7-U)//2;z=(c-2*x-w)//2
    assert (7-2*x,4*x+7*w,2*x+2*z+w)==(U,V,c)
    p7.append([x,z,w])
 for r in range(-isqrt(n),isqrt(n)+1):
  if r%19!=r0 or (n-r*r)%19:continue
  v=(n-r*r)//19
  for c in range(1,isqrt(v)+1,2):
   d0=isqrt(v-c*c)
   if d0*d0!=v-c*c or (r-d0)%2:continue
   for d in sorted({-d0,d0}):p1728.append([r,c,d])
 forms=[]
 for a0 in range(1,isqrt(n//3)+1):
  for b0 in range(-a0,a0+1):
   if (b0*b0+n)%(4*a0):continue
   c0=(b0*b0+n)//(4*a0)
   if a0>c0 or gcd(a0,gcd(b0,c0))!=1 or (a0==c0 or abs(b0)==a0) and b0<0:continue
   forms.append([a0,b0,c0])
 assert len(forms)==len(p7)+len(p1728)
 assert (len(p7),len(p1728))=={47:(3,2),119:(7,3)}[n]
 samples[str(n)]=dict(j7_tangent=s0,j1728_tangent=r0,j7=p7,j1728=p1728,independent_forms=forms)
print(json.dumps(dict(scope="two compatible inert19 seeds and toy multiplicities; no finite trace",
    j7_eta=j7_eta.DATA,j7_index7=j7_index7.DATA,j1728_eta=j1728_eta.DATA,samples=samples),
    indent=2,sort_keys=True))
