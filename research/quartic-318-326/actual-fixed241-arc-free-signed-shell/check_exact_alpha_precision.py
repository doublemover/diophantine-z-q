#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
import json

def prod(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in (0,1)) for j in (0,1)) for i in (0,1))
def inv(A):
 a,b=A[0];c,d=A[1];x=a*d-b*c
 return ((F(d,x),F(-b,x)),(F(-c,x),F(a,x)))
def mod(A,n):return tuple(tuple(int(a)%n for a in z) for z in A)
def vals(A):return [a for z in A for a in z]
I=((1,0),(0,1));A=((2,0),(0,15));B=((1,0),(8,1));C=((1,8),(0,1));L=[]
for P,j,r in ((B,0,2),(C,1,15)):
 Q=mod(prod(prod(P,A),inv(P)),16)
 assert Q[j][j]==r and Q[1-j][j]!=0
 assert all((2*(u-v))%16==0 for u,v in zip(vals(A),vals(Q)))
 assert (Q[0][0]+Q[1][1])%16==1 and (Q[0][0]*Q[1][1]-Q[1][0]*Q[0][1])%16==78%16
 L.append([j,r,Q,mod(tuple(tuple(2*A[i][j]-I[i][j] for j in (0,1)) for i in (0,1)),16)])
root=[r for r in range(16) if (r*r-r+78)%16==0];assert root==[2,15]
ray=[(1,t) for t in range(16)]+[(t,1) for t in range(0,16,2)]
def inZ2(A):return all(a.denominator%2 for a in vals(A))
R=[]
for a,b in ray:
 w=(0,1) if a%2 else (-1,0)
 P=((F(a,16),w[0]),(F(b,16),w[1])); Pinv=inv(P)
 e=next(j for j in range(7) if inZ2(prod(prod(Pinv,((0,-20*2**j),(F(2**j,4),0))),P)))
 R.append([[a,b],e])
assert [r for r,e in R if e==2]==[[0,1],[8,1]]
E=[]
for (a,b),e in R:
 if e!=2:continue
 for k in (1,3):
  r=[r for r in range(16) if ((-80*b*k-r*a)%16,(a*k-r*b)%16)==(0,0)];assert len(r)==1
  r=r[0];assert r==a
  assert {2*m*r*(2*x-1)%32 for m,x in product((241,1205,1687),root)}=={2*r}
  E.append([[a,b],k,r,2*r])
print(json.dumps(dict(scope='static exact alpha-versus-radical and local shell filter; no moving exponent',
 exact_control_roots16=root,adversarial_pairs=L,local_lines_and_target_2_depths=R,actual_equal_depth_aux_eigen_and_x_rows=E),sort_keys=True,separators=(',',':')))
