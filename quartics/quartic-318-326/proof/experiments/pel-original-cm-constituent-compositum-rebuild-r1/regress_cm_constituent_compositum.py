from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from math import prod, gcd
import json
D=[-2,-3,5,-7]
a=[-2,-1,1,-2];b=[0,1,1,1];disc=[-8,-3,5,-7]
def scalar(x):return [Q(x)]+[Q(0)]*15
def unit(i):return [Q(j==(1<<i)) for j in range(16)]
def add(x,y):return [a+b for a,b in zip(x,y)]
def scale(c,x):return [c*a for a in x]
def mul(x,y):
 z=scalar(0)
 for i,xi in enumerate(x):
  for j,yj in enumerate(y):
   if xi and yj:z[i^j]+=xi*yj*prod(D[k] for k in range(4) if (i&j)&(1<<k))
 return z
g=[unit(i) for i in range(4)]
w=[g[0]]+[scale(Q(1,2),add(scalar(1),g[i])) for i in range(1,4)]
for i in range(4):
 assert mul(w[i],w[i])==add(scalar(a[i]),scale(b[i],w[i]))
 assert g[i]==(w[i] if i==0 else add(scale(2,w[i]),scalar(-1)))
# The complete rational product basis, not selected generator points.
basis=[]
for mask in range(16):
 v=scalar(1)
 for i in range(4):
  if mask&(1<<i):v=mul(v,w[i])
 basis.append(v)
def det(M):
 M=[row[:] for row in M];out=Q(1)
 for c in range(len(M)):
  j=next((j for j in range(c,len(M)) if M[j][c]),None)
  if j is None:return Q(0)
  if j!=c:M[c],M[j]=M[j],M[c];out=-out
  pivot=M[c][c];out*=pivot
  for j in range(c+1,len(M)):
   t=M[j][c]/pivot
   for k in range(c,len(M)):M[j][k]-=t*M[c][k]
 return out
coordinate_det=det([[basis[j][i] for j in range(16)] for i in range(16)])
assert coordinate_det==Q(1,2**24)
gram=[[16*mul(x,y)[0] for y in basis] for x in basis]
basis_disc=det(gram)
assert basis_disc==840**8
assert det([[16*mul([Q(j==i) for j in range(16)],[Q(j==k) for j in range(16)])[0] for k in range(16)] for i in range(16)])==basis_disc*2**48
bez=[[0,1,-2,-1],[-3,0,-2,2],[-3,-1,0,3],[1,-1,2,0]]
for i,j in product(range(4),repeat=2):
 if i!=j:assert bez[i][j]*disc[i]+bez[j][i]*disc[j]==1 and gcd(disc[i],disc[j])==1
assert prod(disc)==-840
# Universal coordinate multiplication is checked on a bounded exact grid only.
coordinate_cases=0
for i in range(4):
 for r,s,t,u in product(range(-3,4),repeat=4):
  lhs=mul(add(scalar(r),scale(s,w[i])),add(scalar(t),scale(u,w[i])))
  rhs=add(scalar(r*t+a[i]*s*u),scale(r*u+s*t+b[i]*s*u,w[i]))
  assert lhs==rhs;coordinate_cases+=1
# Negative controls distinguish raw odd generators and the unproved maximality step.
assert all(mul(g[i],g[i])!=add(scalar(a[i]),scale(b[i],g[i])) for i in range(1,4))
assert mul(scale(Q(1,2),add(scalar(1),g[0])),scale(Q(1,2),add(scalar(1),g[0])))!=scalar(-2)
out={'status':'PASS','shifted_equations':4,'inverse_radical_equations':4,'all_product_basis_vectors':16,'coordinate_multiplication_cases':coordinate_cases,'ordered_distinct_bezout_cases':12,'candidate_basis_discriminant':str(basis_disc),'raw_basis_extra_factor':str(2**48),'coordinate_determinant':str(coordinate_det),'negative_controls':4,'scope':'Exact arithmetic consistency only. Does not establish the full integer ring of H, native discriminant, unramifiedness, or Lean acceptance.'}
Path(__file__).with_name('REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
