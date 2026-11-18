"""Independent rational dyadic enclosure of actual real chart embeddings, affine binary addition."""
from math import isqrt
S=1<<2000
class I:
 def __init__(self,x,b=None):
  if b is None:self.a=self.b=x*S
  else:self.a,self.b=x,b
 def __add__(self,o):
  if type(o)==int:o=I(o)
  return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+-o
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  if type(o)==int:o=I(o)
  z=[i*j for i in [self.a,self.b] for j in [o.a,o.b]];return I(min(z)//S,-(-max(z)//S))
 __rmul__=__mul__
 def __truediv__(self,o):
  if type(o)==int:o=I(o)
  assert o.a*o.b>0
  return self*I(S*S//o.b,-(-S*S//o.a))
 def bound(self,d=10**15):return self.a*d//S,-(-self.b*d//S)
def main():
 vals=[]
 for sgn in [1,-1]:
  h=328655617654071015360;r=isqrt(2*S*S);z=sgn*I(r,r+1);d=(3-z)*(3-z);R=(1+z,2*z)
  def plus(P,Q,dbl=False):
   if P is None:return Q
   if Q is None:return P
   x,y=P;X,Y=Q
   l=(3*x*x-d)/(2*y) if dbl else (Y-y)/(X-x)
   a=l*l-x-X;return a,l*(x-a)-y
  P=None
  for i in bin(h)[2:]:
   if P:P=plus(P,P,True)
   if i=='1':P=plus(P,R)
  x,y=P;u=2*y/(x*x+d);vals.append(u)
 return [i.bound() for i in vals+[vals[0]*vals[1]]]
if __name__=='__main__':print(main())
