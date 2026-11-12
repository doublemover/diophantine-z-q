import json,math
c={'cyclic_coordinate_invariance':0,'residue_compatibility':0,'finite_scalar_ring_laws':0,'dual_precomposition':0}
for k in range(8):
 m=2**k
 for u in range(m):
  if math.gcd(u,m)!=1:continue
  v=pow(u,-1,m)
  for a in range(-17,18):
   assert (v*((a*u)%m))%m==a%m
   c['cyclic_coordinate_invariance']+=1
 for a in range(-6,7):
  for b in range(-6,7):
   for x in range(m):
    assert ((a+b)%m*x)%m==(a*x+b*x)%m
    assert ((a*b)%m*x)%m==(a*(b*x))%m
    c['finite_scalar_ring_laws']+=1
    for z in [0,1,3]:
     assert (z*(a*x))%m==(a*z*x)%m
     c['dual_precomposition']+=1
 for j in range(k,9):
  for a in range(-17,18):
   assert (a%(2**j))%m==a%m
   c['residue_compatibility']+=1
print(json.dumps({'status':'PASS','scope':'Exact finite cyclic models of intrinsic endomorphism residues and natural dual scalars; not Lean, topology or global pairing verification','checks':c},indent=2))
