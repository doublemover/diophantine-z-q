from fractions import Fraction as F
import json
K=12
rr=[4376874610839020,101783690143177584,800910366213064752,2642145132961084032,3147690941013049344]
def R(a):
 t=a*(a+1); return sum(c*t**i for i,c in enumerate(rr))
def E(t,b):return (1-b*t*t)*(1-9*b*t*t)/(1+3*b*t*t)**2
def finite(p,b):
 k=12%p
 q=lambda x,y:(y*y-9*b*x*x)%p
 s=lambda x,y:q(x+k*y,y+b*k*x)
 return {x for x in range(p) if q(x,1)==s(x,1)==0}
def main():
 ct=0
 for b in (17,41,73,17*41):
  for t in (F(1,27),F(-27,17),F(4),F(3,2),F(2,7)):
   v=(t+K)/(1+b*K*t)
   q1=1-9*b*t*t; q2=(1+b*K*t)**2-9*b*(t+K)**2
   root=(1+3*b*t*t)/((1+3*b*v*v)*(1+b*K*t)**2*q1)
   assert E(v,b)/E(t,b)==(1-b*K*K)*q1*q2*root**2
   ct+=1
 cases=0
 for p in (5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73):
  for b in range(1,p):
   m=b*K*K%p; hit=finite(p,b)
   if (1-m)%p:
    assert bool(hit)==((25*m-9)%p==0)
   if ((1-m)*(25*m-9))%p==0:assert pow(b,(p-1)//2,p)==1
   cases+=1
 rr605=[a for a in range(605) if a%5 in (1,3) and R(a)%11==0 and R(a)%121!=0]
 assert len(rr605)==80
 print(json.dumps(dict(identity_checks=ct,common_root_checks=cases,mod605_count=len(rr605),examples=[[a,R(a)%121,R(a)%5] for a in (1,3)],obstruction_residues=rr605),indent=2))
if __name__=='__main__':main()
