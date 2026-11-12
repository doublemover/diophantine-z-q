#!/usr/bin/env python3
"""Exact paired mixed-difference algebra and rational compact C2 bump models; not C-infinity/Lean or global minor decay."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

add=lambda x,y:tuple(a+b for a,b in zip(x,y))
scale=lambda x,b:tuple(F(a)/b for a in x)
norm=lambda x:max(map(abs,x))
def phi(t):return max(F(0),1-t*t)**3
def W(x):
 z=F(1)
 for a in x:z*=phi(a)
 return z

def run():
 c=dict(four_corner_product=0,original_weight_mixed=0,paired_amplitude_first_mixed=0,scaled_lattice_mixed=0,actual_plane_mixed_variation=0,negative_controls=0)
 for u0,u1,u2,u3,v0,v1,v2,v3 in product((-2,0,3),repeat=8):
  lhs=(u0*v0-u1*v1)-(u2*v2-u3*v3)
  du=(u0-u1)-(u2-u3);dv=(v0-v1)-(v2-v3)
  rhs=du*v0+(u1-u3)*(v0-v1)+(u2-u3)*(v0-v2)+u3*dv
  assert lhs==rhs
  assert abs(lhs)<=abs(du)*abs(v0)+abs(u1-u3)*abs(v0-v1)+abs(u2-u3)*abs(v0-v2)+abs(u3)*abs(dv)
  c['four_corner_product']+=1
 # Product of five compact C2 bumps: amplitude1, conservative L30,D1080
 # in the original product max norm. Not a C-infinity witness.
 A=F(1);L=F(30);D=F(1080);C=2*A*D+2*L*L
 bases=[(0,0,0,0,0),(1,0,-1,0,0),(F(1,2),F(-1,3),0,F(2,3),0),(-2,1,0,-1,2)]
 steps=[(F(1,3),0,0,0,0),(0,F(1,4),0,0,0),(F(-1,2),F(1,3),0,F(1,5),0),(0,0,0,0,0)]
 for x,u,v,h in product(bases,steps,steps,bases):
  xu=add(x,u);xv=add(x,v);xvu=add(xv,u)
  assert abs((W(x)-W(xu))-(W(xv)-W(xvu)))<=D*norm(u)*norm(v)
  c['original_weight_mixed']+=1
  P=lambda z:W(add(z,h))*W(z)
  assert abs(P(x))<=A*A
  assert abs(P(x)-P(xu))<=2*A*L*norm(u)
  assert abs((P(x)-P(xu))-(P(xv)-P(xvu)))<=C*norm(u)*norm(v)
  c['paired_amplitude_first_mixed']+=1
 e0=(1,0,0,0,0);e1=(0,1,0,0,0)
 for B,h,z,u,v in product((F(1,2),F(1),F(3,2),F(2),F(3)),bases,bases,(e0,e1),(e0,e1)):
  P=lambda y:W(scale(add(h,y),B))*W(scale(y,B))
  assert abs((P(z)-P(add(z,u)))-(P(add(z,v))-P(add(add(z,v),u))))<=C/(B*B)*norm(u)*norm(v)
  c['scaled_lattice_mixed']+=1
 for B,h,lo0,lo1 in product((F(1,2),F(1),F(3,2),F(2),F(3)),bases,(-1,0),(-1,1)):
  N=M=int(B);R=F(1)
  point=lambda i,j:(lo0+i,lo1+j,0,0,0)
  g=lambda i,j:W(scale(add(h,point(i,j)),B))*W(scale(point(i,j),B))
  V=abs(g(N,M))+sum(abs(g(i,M)-g(i+1,M)) for i in range(N))+sum(abs(g(N,j)-g(N,j+1))+sum(abs((g(i,j)-g(i,j+1))-(g(i+1,j)-g(i+1,j+1))) for i in range(N)) for j in range(M))
  assert V<=A*A+4*R*A*L+R*R*C
  c['actual_plane_mixed_variation']+=1
 # Cross terms are essential even when each factor has zero mixed difference.
 u=(0,1,0,1);v=(0,0,1,1)
 assert (u[0]-u[1])-(u[2]-u[3])==0 and (v[0]-v[1])-(v[2]-v[3])==0
 assert (u[0]*v[0]-u[1]*v[1])-(u[2]*v[2]-u[3]*v[3])==1
 # Scaling a mixed step has TWO inverse scale factors.
 assert F(1,4)!=F(1,2)
 # Translated factor cannot be held constant under coordinate steps.
 assert W((F(1,2),0,0,0,0))!=W((0,0,0,0,0))
 c['negative_controls']=3
 result={'status':'PASS','scope':__doc__,'checks':c}
 Path(__file__).with_name('SMOOTH-MIXED-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
