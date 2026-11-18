"""Certified complex modular-Heegner trace, control D=-23 (96-bit output is ample)."""
from flint import acb,arb,ctx
import json
ctx.prec=160
T=1800
f=[0,1]+[0]*(T-1)
for k in (2,4,6,12):
 for j in range(k,T+1,k):
  for m in range(T,j-1,-1):f[m]-=f[m-j]
g=[u*(-1 if k%4==3 else 1) for k,u in enumerate(f)]
A=[(u+v)//2 for u,v in zip(f,g)]
B=[f[i//2] if i%2==0 else 0 for i in range(T+1)]
def cm(a,b,c):
 assert b*b-4*a*c==-23 and a%48==0 and (b-13)%96==0
 q=(acb(-arb(23).sqrt(),-b)*arb.pi()/a).exp()
 r=q.abs_upper(); assert r<1
 t=T+1
 tail=2*r**t*(t*t/(1-r)+2*t*r/(1-r)**2+r*(1+r)/(1-r)**3)
 err=arb(0,tail.upper())
 powers=[q**m for m in range(T+1)]
 def fourier(cs,deriv=False):
  z=acb(0)
  for m in range(T+1):
   if cs[m]: z+=powers[m]*int(cs[m])*(m if deriv else 1)
  return z+acb(err,err)
 A0,B0=fourier(A),fourier(B)
 x=B0/A0; y=(A0*fourier(B,True)-B0*fourier(A,True))/A0**3
 t=x-1/x;w=y/(x*x);X=(w+t*t+2)/2;Y=t*X
 assert (Y*Y-X*(X+1)*(X-3)).contains(0) and Y.is_finite()
 return X,Y
def add(P,Q):
 x,y=P;X,Y=Q
 assert not (X-x).contains(0)
 s=(Y-y)/(X-x);v=s*s+2-x-X
 return v,s*(x-v)-y
def double(P):
 x,y=P
 assert not y.contains(0)
 s=(3*x*x-4*x-3)/(2*y);v=s*s+2-2*x
 return v,s*(x-v)-y
forms=[(48,13,1),(96,-83,18),(144,-83,12)]
if __name__=='__main__':
 P=[cm(*h) for h in forms]
 R=add(add(P[0],P[1]),P[2]);U=double(R)
 assert U[0].imag.contains(0) and U[1].real.contains(0) and not U[1].imag.contains(0)
 V=double(U);assert V[0].is_finite() and V[1].is_finite()
 print(json.dumps(dict(discriminant=-23,level=48,precision=ctx.prec,T=T,
   forms=forms,trace=[str(z) for z in R],twice_trace=[str(z) for z in U],
   four_times_trace_is_affine=True),indent=2))
