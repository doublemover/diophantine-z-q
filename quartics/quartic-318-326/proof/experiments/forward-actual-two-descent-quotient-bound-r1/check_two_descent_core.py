"""Independent exact F2 and rational regressions, not a Lean compilation."""
import itertools,random,json
from fractions import Fraction as F
rng=random.Random(731)
def rank(a):
 a=[r[:] for r in a];n=len(a);k=0
 for j in range(n):
  p=next((i for i in range(k,n) if a[i][j]),None)
  if p is None:continue
  a[k],a[p]=a[p],a[k]
  for i in range(n):
   if i!=k and a[i][j]:a[i]=[x^y for x,y in zip(a[i],a[k])]
  k+=1
 return k
def core(D):
 d=len(D)-1;C=[[int(i==j or i==d) for j in range(d)] for i in range(d+1)]
 return [D[i]+C[i] for i in range(d+1)]+[[C[i][j] for i in range(d+1)]+[0]*d for j in range(d)]
cores=0
for d in range(3):
 for bits in itertools.product([0,1],repeat=(d+1)**2):
  if sum(bits)%2!=1:continue
  D=[list(bits[i*(d+1):(i+1)*(d+1)]) for i in range(d+1)];M=core(D)
  assert rank(M)==len(M);cores+=1
extensions=0
for d in range(1,7):
 for trial in range(20):
  D=[[rng.randrange(2) for _ in range(d+1)] for _ in range(d+1)]
  D[0][0]^=(sum(map(sum,D))+1)%2
  A=core(D);assert rank(A)==len(A);cores+=1
  original=[r[:] for r in A]
  n0=len(A)
  for step in range(6):
   n=len(A);row=[rng.randrange(2) for _ in range(n)];col=[rng.randrange(2) for _ in range(n)]
   candidates=[[A[i]+[col[i]] for i in range(n)]+[row+[bit]] for bit in [0,1]]
   good=[M for M in candidates if rank(M)==n+1]
   assert len(good)==1
   A=good[0]
   assert [r[:n0] for r in A[:n0]]==original
   assert A[-1][:-1]==row and [A[i][-1] for i in range(n)]==col
   extensions+=1
points=0
for t in [F(a,b) for a in range(1,16) for b in range(1,8)]:
 beta=F(17);r=F(1);v=-68*t/(3+17*t*t);u=(6-34*t*t)/(3+17*t*t)
 n=17-v*v;x=17;y=beta*r*u*v
 if not u*v:continue
 assert x+3*n==beta*u*u and x-n==v*v
 assert y*y==x*(x-n)*(x+3*n)
 extracted=y/(beta*u*v)
 assert beta*extracted**2==x and extracted
 points+=1
primes=0
import math
def prime(p):return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
for m in [5,7,11,17,35,55]:
 for a in range(m):
  if math.gcd(a,m)!=1:continue
  for v in [1,7]:
   p=next(p for p in range(101,100000) if p%m==a and p%12==v and prime(p))
   assert p>100 and math.gcd(p,m*12)==1
   primes+=1
print(json.dumps({'status':'PASS','nonsingular_exact_core_cases':cores,'finite_support_preserving_diagonal_steps':extensions,'exact_rational_kummer_extractions':points,'fresh_CRT_type_prime_cases':primes,'scope':'Actual matrix and extraction regressions. Rational samples are not the four source-index points. No Selmer/global rational-point existence is inferred.'},indent=2))
