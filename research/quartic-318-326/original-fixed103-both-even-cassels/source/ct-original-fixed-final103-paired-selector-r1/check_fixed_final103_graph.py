#!/usr/bin/env python3
"""Finite exact GF2 Schur gates; no arithmetic source materialization."""
from itertools import product
from math import isqrt,gcd
import json
rows={}
def bit(M,i,j): return (M[i]>>j)&1
def inv(M):
 n=len(M);S=M[:];P=[1<<i for i in range(n)]
 for j in range(n):
  k=next((k for k in range(j,n) if bit(S,k,j)),None)
  if k is None:return None
  S[j],S[k]=S[k],S[j];P[j],P[k]=P[k],P[j]
  for k in range(n):
   if k!=j and bit(S,k,j):S[k]^=S[j];P[k]^=P[j]
 return P
def mm(A,B):
 def one(x):
  y=0
  for j,b in enumerate(B):
   if (x>>j)&1:y^=b
  return y
 return [one(x) for x in A]
def schur(A,L):
 n=len(A);m=n-L
 U=[a&((1<<L)-1) for a in A[:L]]
 W=[a>>L for a in A[:L]]
 V=[a&((1<<L)-1) for a in A[L:]]
 H=[a>>L for a in A[L:]]
 assert inv(H) is not None
 return [a^b for a,b in zip(U,mm(mm(W,inv(H)),V))]
def lap(n,edg):
 S=[0]*n
 for a,b in edg:
  e=(1<<a)|(1<<b);S[a]^=e;S[b]^=e
 return S
I=lambda n:[1<<k for k in range(n)]
def plus(A,B):return [a^b for a,b in zip(A,B)]
def cut(A, omit):
 keep=[i for i in range(len(A)) if i not in omit]
 return [sum(bit(A,i,j)<<k for k,j in enumerate(keep)) for i in keep]
def qr(a,p):return pow(a%p,(p-1)//2,p)==1
assert 103%24==7 and qr(17,103) and qr(2,103) and not any(103%i==0 for i in range(2,11))
rows['source']=[103,17,1751,103%24]
h=0
for a in range(1,isqrt(1751//3)+1):
 for b in range(-a,a+1):
  if (b*b+1751)%(4*a):continue
  c=(b*b+1751)//(4*a)
  if a<=c and ((abs(b)!=a and a!=c) or b>=0) and gcd(a,b,c)==1:h+=1
assert h==48;rows['fixed_cm_class_number']=h
# four-node toggle; old nodes 0=i,1=j,2=17, q0=7
Ed=[(0,3),(0,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,5)]+[(q,7) for q in range(3,7)]
N=schur(cut(lap(8,Ed),[7]),3)
C=schur(lap(6,[(i if i<2 else i-1,j if j<2 else j-1) for i,j in Ed if 2 not in (i,j) and 7 not in (i,j)]),2)
assert N==[3,3,0] and C==[3,3];rows['four_node_d_edge']=[N,C]
# star toggle old 0=i,1=17; helpers 2,3 and q0=4.
Ed=[(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)]
N=schur(cut(lap(5,Ed),[4]),2);C=schur(lap(3,[(0,1),(0,2),(1,2)]),1)
assert N==[3,3] and C==[0];rows['two_node_star_edge']=[N,C]
# θ toggler old 0=v,1=j; a,b,a',b'=2,3,4,5; q0=6.
es=[(0,2),(2,3),(3,6),(0,4),(4,5),(5,6)]
F=schur(cut(lap(7,es),[6]),2); S=schur(cut(lap(7,es+[(1,2)]),[6]),2)
assert F==[0,0] and S==[0,2];rows['connected_companion_toggle']=[F,S]
# Abstract check of generalized type-one block plus fixed q0 and actual selected type5 r.
# Every invertible sharp matrix with beta^T C=e17^T tolerates that rank-one update.
checks=0
for M in product(range(16),repeat=4):
 A=list(M)
 if (A[0]^A[1]^A[2])!=1 or inv(A) is None:continue
 B=A[:];B[3]^=1
 assert inv(B) is not None;checks+=1
rows['type5_anchor_rank_one_cases']=checks
print(json.dumps(rows,sort_keys=True))
