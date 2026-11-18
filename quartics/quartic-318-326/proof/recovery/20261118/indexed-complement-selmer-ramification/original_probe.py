from functools import lru_cache
from math import gcd,lcm,isqrt
import json
from pathlib import Path
data=json.loads(Path(__file__).with_name("INPUTS.json").read_text())
h=328655617654071015360;g=1094218652709755;r=4*g;A=114444*r; J=h*g**8*11*17;m=6**21*3**65536*J;beta=17*11*g
def probe(p,j=1,forceM=None):
 M=int(data["annihilators"][str(p)]) if forceM is None else forceM;v=p**j
 def K(a,b=0):return(a%v,b%v)
 def add(x,y):return K(x[0]+y[0],x[1]+y[1])
 def sub(x,y):return K(x[0]-y[0],x[1]-y[1])
 def mul(x,y):return K(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
 def norm(x):return (x[0]**2-2*x[1]**2)%v
 def cube(x):return mul(x,mul(x,x))
 def sq(x):return mul(x,x)
 def n(x,k):return K(x[0]*k,x[1]*k)
 def div(x,y):
  z=norm(y)
  if z%p==0:raise ValueError
  return n(mul(x,(y[0],-y[1])),pow(z,-1,v))
 x=K(1,1);y=K(0,2);a=K(-11,6);x2=sq(x);x4=sq(x2);a2=sq(a);i2y=div(K(1),n(y,2))
 tab=[K(0),K(1),n(y,2),sub(add(n(x4,3),n(mul(a,x2),6)),a2),
  mul(n(y,4),sub(sub(add(mul(x4,x2),n(mul(a,x4),5)),n(mul(a2,x2),5)),mul(a2,a)))]
 @lru_cache(None)
 def psi(i):
  if i<5:return tab[i]
  k=i//2
  if i%2:return sub(mul(psi(k+2),cube(psi(k))),mul(psi(k-1),cube(psi(k+1))))
  return mul(mul(psi(k),i2y),sub(mul(psi(k+2),sq(psi(k-1))),mul(psi(k-2),sq(psi(k+1)))))
 def Usq(i):
  if not i:return K(0)
  z=sq(psi(i));return div(z,sub(mul(x,z),mul(psi(i-1),psi(i+1))))
 M*=p**(j-1)
 assert psi(M)==K(0) and norm(mul(psi(M-1),psi(M+1)))%p, ('annihilator failed',p,j)
 try:
  UH=Usq((2*h)%M);Um=Usq((2*m)%M)
  N=norm(add(K(1),div(UH,K(r))))
  if norm(UH)%p:
   ratio=norm(div(Um,UH))
  elif UH[0]%p==UH[1]%p==0:
   ratio=pow(m//h,4,v)
  else:raise ValueError('mixed formal component not used in certificate')
  q2=ratio*pow(r,-30,v)%v
  W=(N*N+r*q2)%v; D=(1-A*W*W*pow(17*(1+A)**2,-1,v))%v
 except ValueError:return None
 return {'p':p,'ring_modulus':v,'M':M,'2hR_index':2*h%M,'2mR_index':2*m%M,'UH2':UH,'Um2':Um,'N':N,'Q2':q2,'W':W,'D':D}
