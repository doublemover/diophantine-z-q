from math import prod
import json
bs=[5,11,17,163,661,733,1489,1861]
h=328655617654071015360;g=1094218652709755;r=4*g;A=114444*r;beta=prod(bs)
assert beta==17*11*g
def formal(p):
 assert pow(2,(p-1)//2,p)==p-1
 k=lambda a,b=0:(a%p,b%p)
 def sub(x,y):return k(x[0]-y[0],x[1]-y[1])
 def mul(x,y):return k(x[0]*y[0]+2*x[1]*y[1],x[1]*y[0]+x[0]*y[1])
 def div(x,y):
  a,b=y
  return mul(x,mul(k(a,-b),k(pow((a*a-2*b*b)%p,-1,p))))
 def plus(P,Q):
  if P is None:return Q
  if Q is None:return P
  x,y=P;u,v=Q
  if x==u:
   if y==k(-v[0],-v[1]):return None
   assert y==v
   lam=div(sub(mul(k(3),mul(x,x)),k(11,-6)),mul(k(2),y))
  else:lam=div(sub(v,y),sub(u,x))
  z=sub(sub(mul(lam,lam),x),u)
  return z,sub(mul(lam,sub(x,z)),y)
 P=(k(1,1),k(0,2));Q=None;t=2*h
 while t:
  if t%2:Q=plus(Q,P)
  t//=2;P=plus(P,P)
 return Q is None
def residues(p):
 assert formal(p)
 k=p*p;moh=pow(6,21,k)*pow(3,65536,k)*pow(g,8,k)*11*17%k
 q2=pow(moh,4,k)*pow(r,-30,k)%k
 w=(1+r*q2)%k
 D=(1-A*w*w*pow(17*(1+A)**2,-1,k))%k
 out=dict(q2=q2,w=w,D=D)
 if p==13:
  assert w%p==0 and w//p and D%p==1
  out['R_div_p2']=A*(w//p)**2*pow(17*(1+A)**2,-1,p)%p
  out['p2H']=3*pow(out['R_div_p2'],-1,p)%p
 if p==179:assert (4-D)%p==0 and (4-D)%k
 return out
if __name__=='__main__':print(json.dumps({p:residues(p) for p in [13,179]},indent=2))
