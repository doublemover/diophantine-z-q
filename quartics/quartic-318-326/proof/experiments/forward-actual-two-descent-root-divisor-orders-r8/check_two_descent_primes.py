"""Independent finite F2/symbol regressions; no rational existence claim."""
import itertools,random,json,math
rng=random.Random(11731)
def prime(q):return q>=2 and all(q%d for d in range(2,math.isqrt(q)+1))
def chi(a,p):
 x=pow(a%p,(p-1)//2,p)
 return -1 if x==p-1 else x
prime_cases=0
old=[5,7,11,17]
for k in range(5):
 ps=old[:k]
 for bits in itertools.product([0,1],repeat=k):
  for special in [False,True]:
   typ=7 if special else 1
   q=next(q for q in range(101,300000,2) if q%12==typ and prime(q) and all(chi(q,p)==(-1 if b else 1) for p,b in zip(ps,bits)))
   assert q not in ps
   for p,b in zip(ps,bits):
    assert chi(p,q)==(-1)**((p//2)*(q//2))*(-1 if b else 1)
   prime_cases+=1
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
def mv(M,x):return tuple(sum(a*b for a,b in zip(row,x))%2 for row in M)
matrices=vectors=0
for n in range(1,6):
 for trial in range(12):
  while True:
   A=[[rng.randrange(2) for _ in range(n)] for _ in range(n)]
   if rank(A)==n:break
  # q0 is the last entry, matching Option.none up to index order.
  M=[row+[sum(row)%2] for row in A]+[[sum(A[i][j] for i in range(n))%2 for j in range(n)]+[sum(map(sum,A))%2]]
  v=[1]+[rng.randrange(2) for _ in range(n-1)]+[0]
  one=[1]*(n+1);lam=mv(M,v)
  span={tuple(c^ (d*t) for t in v) for c,d in itertools.product([0,1],repeat=2)}
  assert len(span)==4 and lam!=tuple([0]*(n+1))
  for x in itertools.product([0,1],repeat=n+1):
   a=x[0]^x[-1];Tx=[z^(a*t) for z,t in zip(x,v)]
   Kx=mv(M,Tx)
   assert (Kx==tuple([0]*(n+1)))==(x in span)
   assert Kx!=lam
   assert (mv(M,x)==tuple([0]*(n+1)))==(x==tuple(one) or x==tuple([0]*(n+1)))
   vectors+=1
  matrices+=1
print(json.dumps({'status':'PASS','all_prescribed_prime_and_reverse_symbol_cases':prime_cases,'actual_completion_projection_cases':matrices,'exhaustive_kernel_image_vector_checks':vectors,'scope':'Finite regressions of constructed prime-symbol and exact matrix steps only. Does not prove Selmer interpretation or four rational point existence.'},indent=2))
