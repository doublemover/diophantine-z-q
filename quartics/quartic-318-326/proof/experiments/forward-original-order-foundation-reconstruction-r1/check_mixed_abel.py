#!/usr/bin/env python3
"""Exact real-rational mixed Abel bounds, Gaussian-integer identities and original plane-phase coverage; not Lean/global decay."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def prefix(f,n):return sum(f(i) for i in range(n))
def weighted(f,g,n):return sum(g(i)*f(i) for i in range(n))
def variation(g,n):return abs(g(n))+sum(abs(g(i)-g(i+1)) for i in range(n))
def mixed(g,n,m):return variation(lambda i:g(i,m),n)+sum(variation(lambda i:g(i,j)-g(i,j+1),n) for j in range(m))
def rect(f,k,g,n,m):return sum(g(i,j)*f(i)*k(j) for i in range(n) for j in range(m))
def psum(q,terms):
 a=[0]*q
 for phase,weight in terms:a[phase%q]+=weight
 return a

def run():
 c=dict(real_abel_identity_and_bound=0,gaussian_integer_identity=0,mixed_difference_budget=0,scaled_mixed_variation=0,original_two_axis_identity=0,original_plane_phase_factor=0,negative_controls=0)
 for n,m in product(range(6),repeat=2):
  for mode in range(3):
   f=lambda i:(-1)**i*(i%3+1)
   k=lambda j:(-1)**(j//2)*(j%2+1)
   g=lambda i,j: (F(1+i*j-i+2*j,3) if mode==0 else F((-1)**(i+j)) if mode==1 else F(2*i*j+i*i-3*j*j))
   actual=rect(f,k,g,n+1,m+1)
   abel=weighted(f,lambda i:g(i,m),n+1)*prefix(k,m+1)+sum(weighted(f,lambda i:g(i,j)-g(i,j+1),n+1)*prefix(k,j+1) for j in range(m))
   assert actual==abel
   A=max(abs(prefix(f,u)) for u in range(n+2));B=max(abs(prefix(k,v)) for v in range(m+2))
   assert abs(actual)<=A*B*mixed(g,n,m)
   c['real_abel_identity_and_bound']+=1
   d0=max([abs(g(i,m)-g(i+1,m)) for i in range(n)]+[F(0)])
   d1=max([abs(g(n,j)-g(n,j+1)) for j in range(m)]+[F(0)])
   d01=max([abs((g(i,j)-g(i,j+1))-(g(i+1,j)-g(i+1,j+1))) for i in range(n) for j in range(m)]+[F(0)])
   assert mixed(g,n,m)<=abs(g(n,m))+n*d0+m*d1+n*m*d01
   c['mixed_difference_budget']+=1
  # Gaussian integers stay exactly representable in this small finite test.
  f=lambda i:(1j)**i;k=lambda j:(-1j)**j;g=lambda i,j:complex(i*j+2,2*i-j*j)
  assert rect(f,k,g,n+1,m+1)==weighted(f,lambda i:g(i,m),n+1)*prefix(k,m+1)+sum(weighted(f,lambda i:g(i,j)-g(i,j+1),n+1)*prefix(k,j+1) for j in range(m))
  c['gaussian_integer_identity']+=1
 for B in (F(1),F(3,2),F(2),F(7,2),F(5)):
  for n,m in product(range(int(B)+1),repeat=2):
   g=lambda i,j:1+F(i)*j/(B*B)
   assert abs(g(n,m))<=2
   assert all(abs(g(i,m)-g(i+1,m))<=1/B for i in range(n))
   assert all(abs(g(n,j)-g(n,j+1))<=1/B for j in range(m))
   assert all(abs((g(i,j)-g(i,j+1))-(g(i+1,j)-g(i+1,j+1)))<=1/(B*B) for i in range(n) for j in range(m))
   assert mixed(g,n,m)<=5
   c['scaled_mixed_variation']+=1
 add=lambda x,y:tuple(a+b for a,b in zip(x,y))
 w=lambda z:1+sum((i+1)*a*a-(i+2)*a for i,a in enumerate(z))+z[0]*z[1]
 bil=lambda K,h,z:h[0]*z[0]+h[1]*z[1]-h[2]*z[2]-h[3]*z[3]-K*h[4]*z[4]
 for K,h,lo0,lo1,n,m,q in product((-3,0,2),[(1,-2,1,0,2),(0,0,0,0,0)],(-2,1),(-1,2),(0,1,4),(0,2,3),(1,2,3,5)):
  base=(lo0,lo1,1,-1,2)
  plane=lambda i,j:(lo0+i,lo1+j,1,-1,2)
  actual=psum(q,((2*bil(K,h,plane(i,j)),w(add(h,plane(i,j)))*w(plane(i,j))) for i in range(n) for j in range(m)))
  intervals=psum(q,((2*bil(K,h,(a,b,1,-1,2)),w(add(h,(a,b,1,-1,2)))*w((a,b,1,-1,2))) for b in range(lo1,lo1+m) for a in range(lo0,lo0+n)))
  factored=psum(q,((2*bil(K,h,base)+2*h[0]*i+2*h[1]*j,w(add(h,plane(i,j)))*w(plane(i,j))) for i in range(n) for j in range(m)))
  assert actual==intervals;assert actual==factored
  c['original_two_axis_identity']+=1;c['original_plane_phase_factor']+=1
 g=lambda i,j:F(i*j)
 assert mixed(g,1,1)>abs(g(1,1))+abs(g(0,1)-g(1,1))+abs(g(1,0)-g(1,1))
 assert (1+0*0)*(1+1*1)!=(1+0*1)*(1+1*0)
 assert 2%3!=1%3
 assert (1+1j)*(1-1j)!=(1+1j)*(1+1j)
 c['negative_controls']=4
 result={'status':'PASS','scope':__doc__,'checks':c}
 Path(__file__).with_name('MIXED-ABEL-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
