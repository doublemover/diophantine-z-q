import itertools,json
rings=finite=0
for p in [2,3,5]:
 E=list(itertools.product(range(p),repeat=2))
 def add(a,b):return ((a[0]+b[0])%p,(a[1]+b[1])%p)
 def mul(a,b):return (a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)
 for a,b in itertools.product(E,repeat=2):
  residue_nonzero=(a[0]!=0 or b[0]!=0)
  unit_ideal=any(add(mul(a,u),mul(b,v))==(1,0) for u,v in itertools.product(E,repeat=2))
  assert residue_nonzero==unit_ideal;rings+=1
 # Nonzero nilpotent fails the residue/unit test.
 assert (0,1)!=(0,0) and not any(mul((0,1),u)==(1,0) for u in E)
for nx in range(4):
 for ny in range(4):
  X=range(nx);Y=range(ny)
  for f in itertools.product(Y,repeat=nx):
   for bits in itertools.product([False,True],repeat=ny):
    U={y for y in Y if bits[y]}
    local=all(f[x] in U for x in X)
    lifts=[g for g in itertools.product(U,repeat=nx) if g==f]
    assert local==(len(lifts)==1);finite+=1
print(json.dumps({'dual_number_coordinate_cases':rings,'finite_whole_factorization_cases':finite,'nilpotent_negative_controls':3,'scope':'Finite ancillary models, not a scheme or Lean test'}))
