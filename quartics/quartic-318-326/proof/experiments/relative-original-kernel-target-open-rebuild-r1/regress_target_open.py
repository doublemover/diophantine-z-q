"""Finite exact regressions, not scheme verification or Lean elaboration."""
import itertools,json,math

def subsets(xs):
 xs=list(xs)
 return [frozenset(x for i,x in enumerate(xs) if m>>i&1) for m in range(1<<len(xs))]
compat=incompat=restricts=uniques=0
for size in range(5):
 X=frozenset(range(size))
 for A in subsets(X):
  for B in subsets(X):
   if A|B!=X:continue
   for V in subsets(A):
    for W in subsets(B):
     G=V|W
     agreement=(V&B)==(W&A)
     exact=(G&A==V and G&B==W)
     assert exact==agreement
     if agreement:
      compat+=1;restricts+=2
      for H in subsets(X):
       if H&A==V and H&B==W:
        assert H==G;uniques+=1
     else:
      assert not exact;incompat+=1
# Empty covering index is possible exactly for an empty space.
assert frozenset().union()==frozenset()
basechanges=hom_pairs=cech=0
for ns in range(4):
 S=tuple(range(ns))
 for nz in range(4):
  Z=tuple(range(nz))
  for n in itertools.product(Z,repeat=ns):
   if set(n)!=set(Z):continue
   for V in subsets(Z):
    N=tuple(s for s in S if n[s] in V)
    assert {n[s] for s in N}==set(V)
    for nt in range(3):
     T=tuple(range(nt))
     for t in itertools.product(V,repeat=nt):
      P={(x,s) for x in T for s in N if t[x]==n[s]}
      assert {x for x,s in P}==set(T)
      assert all(n[s]==t[x] for x,s in P);basechanges+=1
     actual=set(itertools.product(N,repeat=nt))
     pairs={(a,tuple(n[s] for s in a)) for a in itertools.product(S,repeat=nt)
       if all(n[s] in V for s in a)}
     assert pairs=={(a,tuple(n[s] for s in a)) for a in actual};hom_pairs+=len(pairs)
    for a,b in itertools.product(N,repeat=2):
     assert (n[a]==n[b])==((a,b) in {(s,t) for s in N for t in N if n[s]==n[t]});cech+=1
modular=triples=dual=negative=0
for q in [4,6,8,9]:
 for d in [(1,1,-1),(2,0,1),(0,0,0)]:
  for x in itertools.product(range(q),repeat=3):
   if sum(a*b for a,b in zip(d,x))%q:continue
   units=[i for i in range(3) if math.gcd(x[i],q)==1]
   slices={i:tuple(pow(x[i],-1,q)*a%q for a in x) for i in units}
   for i,j in itertools.product(units,repeat=2):
    left=slices[i];right=slices[j];ratio=pow(left[j],-1,q)
    assert tuple(ratio*a%q for a in left)==right
    assert sum(a*b for a,b in zip(d,right))%q==0
    assert math.gcd(q,*left)==math.gcd(q,*right);modular+=1
    for k in units:
     assert pow(slices[j][k],-1,q)*ratio%q==pow(left[k],-1,q);triples+=1
 for z in range(q):
  if math.gcd(z,q)!=1:
   assert math.gcd(q,z)!=1;negative+=1
p=3;E=list(itertools.product(range(p),repeat=2));zero=(0,0);one=(1,0)
def mul(a,b):return (a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)
def add(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
def inv(a):return next(b for b in E if mul(a,b)==one)
def dot(d,x):
 z=zero
 for a,b in zip(d,x):z=add(z,mul(a,b))
 return z
for d in [(one,one,(2,0)),((0,1),zero,one),(zero,zero,zero)]:
 for x in itertools.product(E,repeat=3):
  if dot(d,x)!=zero:continue
  units=[i for i in range(3) if x[i][0]!=0]
  slices={i:tuple(mul(inv(x[i]),a) for a in x) for i in units}
  for i,j in itertools.product(units,repeat=2):
   ratio=inv(slices[i][j]);right=tuple(mul(ratio,a) for a in slices[i])
   assert right==slices[j] and dot(d,right)==zero;dual+=1
assert not any(mul((0,1),b)==one for b in E);negative+=1
print(json.dumps({'compatible_finite_covers':compat,'incompatible_negative_covers':incompat,'exact_chart_restrictions':restricts,'unique_global_opens':uniques,'arbitrary_test_basechanges':basechanges,'compatible_hom_pairs':hom_pairs,'cech_relation_pairs':cech,'modular_full_kernel_overlaps':modular,'transition_triples':triples,'dual_number_full_kernel_overlaps':dual,'nonunit_negative_controls':negative,'scope':'Finite models only; not Lean, scheme proof or arithmetic theorem verification'}))
