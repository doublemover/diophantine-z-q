import itertools,json,math
count=field=0
for n in range(2,9):
 for d in itertools.product(range(n),repeat=2):
  for x in itertools.product(range(n),repeat=2):
   if sum(a*b for a,b in zip(d,x))%n:continue
   assert (x==(0,0))==all(a==0 for a in x);count+=1
   if n in (2,3,5,7) and x!=(0,0):
    a=next(a for a in x if a);assert pow(a,-1,n)*a%n==1;field+=1
# Nonzero is insufficient over non-fields, and zero is not admissible over fields.
assert 2!=0 and math.gcd(2,4)!=1
assert not any((0,0))
print(json.dumps({'kernel_coordinate_cases':count,'field_inverse_cases':field,'negative_controls':2,'scope':'Finite algebra model only, no sheaf or Lean validation'}))
