import itertools,json,math
cases=zeros=negatives=0
for n in [4,6,8,9]:
 U=[a for a in range(n) if math.gcd(a,n)==1]
 def ideal(x):return {sum(a*b for a,b in zip(x,c))%n for c in itertools.product(range(n),repeat=len(x))}
 for d in itertools.product(range(n),repeat=2):
  for x in itertools.product(range(n),repeat=2):
   if sum(a*b for a,b in zip(d,x))%n:continue
   for i in range(2):
    if x[i] not in U:continue
    u=x[i];z=tuple(pow(u,-1,n)*a%n for a in x)
    assert z[i]==1 and sum(a*b for a,b in zip(d,z))%n==0
    assert tuple(u*a%n for a in z)==x
    assert ideal(x)==ideal(z);cases+=1
 for t in U:
  for x in itertools.product(range(n),repeat=2):
   assert ideal(x)==ideal(tuple(t*a%n for a in x));zeros+=1
 for t in range(n):
  if t not in U:
   assert ideal((1,0))!=ideal((t,0));negatives+=1
# A square-zero ring tests genuine nonreduced equations and full ideals.
p=3;E=list(itertools.product(range(p),repeat=2));zero=(0,0);one=(1,0)
def add(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
def mul(a,b):return (a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)
def dot(x,y):return add(mul(x[0],y[0]),mul(x[1],y[1]))
def ideal(x):return {dot(x,c) for c in itertools.product(E,repeat=2)}
dual=0
for d in itertools.product(E,repeat=2):
 for x in itertools.product(E,repeat=2):
  if dot(d,x)!=zero:continue
  for i in range(2):
   u=x[i]
   if u[0]==0:continue
   inv=next(v for v in E if mul(u,v)==one)
   z=tuple(mul(inv,a) for a in x)
   assert z[i]==one and dot(d,z)==zero
   assert tuple(mul(u,a) for a in z)==x and ideal(x)==ideal(z);dual+=1
assert ideal((one,zero))!=ideal(((0,1),zero));negatives+=1
print(json.dumps({'modular_kernel_normalizations':cases,'unit_full_ideal_equalities':zeros,'dual_number_kernel_normalizations':dual,'nonunit_negative_controls':negatives,'scope':'Ancillary finite-ring models, not Lean or scheme verification'}))
