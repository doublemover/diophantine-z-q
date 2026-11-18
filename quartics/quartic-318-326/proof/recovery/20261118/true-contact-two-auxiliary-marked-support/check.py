"""Finite tests for the exact signed roots and two simultaneous reduced support constructions (no search for an indexed h)."""
import random,json,itertools,math
from fractions import Fraction as Q
def rank(rows):
 bs={}
 for row in rows:
  x=sum(t<<i for i,t in enumerate(row))
  while x and x.bit_length() in bs:x^=bs[x.bit_length()]
  if x:bs[x.bit_length()]=x
 return len(bs)
def red(w):
 v={}
 for p in (2,3,5,7,11,17,37,2399):
  b=0
  while w%p==0:w//=p;b^=1
  v[p]=b
 assert w==1
 return v
rt=list(map(Q,['0','-1/2','-1','1/2399','-32/407']))
edges=[]
for i,j in itertools.combinations(range(5),2):
 d=abs(rt[i]-rt[j]); bits=red(d.numerator*d.denominator)
 if bits[7]^bits[2399]:edges.append((i,j))
assert edges==[(0,3),(1,3),(1,4),(2,3)]
assert all(2399%k for k in range(2,math.isqrt(2399)+1)) and pow(26,1199,2399)==2398
tree=[[0]*6 for _ in range(6)]
for i,j in edges:tree[i+1][j+1]=tree[j+1][i+1]=1
for i in range(6):tree[i][i]=sum(tree[i])%2
tree[0][0]=1
rng=random.Random(1702399)
def extend(A,col,row,diag):
 return [r+[a] for r,a in zip(A,col)] + [row+[diag]]
def rand(n):return [rng.randrange(2) for _ in range(n)]
def solve(R,cols,rows,lower,notes):
 A=[r[:] for r in R]
 for j in range(len(cols)):
  C=cols[j]+[lower[i][j] for i in range(j)]
  V=rows[j]+lower[j][:j]
  opts=[v for v in [0,1] if rank(extend(A,C,V,v))==len(A)+1]
  assert opts
  A=extend(A,C,V,opts[0]);notes.append(opts[0])
 return A
def dot(a,b):return sum(x*y for x,y in zip(a,b))%2
q1=[1,1,0,0,0,0]
old=extend(tree,q1,q1,0);assert rank(old)==7 and rank(tree)==5
h=[0,1,1,1,1,1]
for _ in range(400):
 l=rng.randint(2,8);X=[]
 for j in range(l):
  # beta is local square at every new prime. Ensure two bridge cols.
  v=rand(5)
  if j<2 and sum(v)%2==0:v[0]^=1
  X+=[[sum(v)%2]+v]
 # The optional partition has one independent bridge in each part.
 for br,js in [(0,[j for j in range(2,l) if j%2==0]),(1,[j for j in range(2,l) if j%2])]:
  c=X[br];rr=c[:];rr[0]^=rng.randrange(2)
  assert dot(c,h)==dot(rr,h)==1
  for z in [0,1]:
   R=extend(tree,c,rr,z);assert rank(R)==7
   cs=[X[j]+rand(1) for j in js];rs=[x[:] for x in cs]
   for y in rs:y[0]^=rng.randrange(2);y[-1]^=rng.randrange(2)
   A=solve(R,cs,rs,[rand(len(js)) for j in js],[]);assert rank(A)==len(A)
 # Two aux: q1-theta zeros, arbitrary inhomogeneous internal blocks incl reciprocity.
 cs=[x+[0] for x in X];rs=[x[:] for x in cs]
 for y in rs:y[0]^=rng.randrange(2)
 A=solve(old,cs,rs,[rand(l) for _ in range(l)],[]);assert rank(A)==len(A)
print(json.dumps({'negative_edges':edges,'tree_cofactor':1,'two_aux_old_minor_rank':7,'one_aux_beta_rank':5,'random_bordered_minor_trials':400,'is_original_grid':False},sort_keys=True,indent=2))
