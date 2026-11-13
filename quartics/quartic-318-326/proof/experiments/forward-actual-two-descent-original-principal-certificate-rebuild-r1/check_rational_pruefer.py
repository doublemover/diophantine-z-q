import json,math
checks={'finite_factor_transition':0,'free_coordinate_transition':0,'cyclic_involutions':0,'free_generator_nonzero':0}
for m in range(1,65):
 a=0
 while m%(2**(a+1))==0:a+=1
 for k in range(0,9):
  target=math.gcd(2**(k+a),m)
  for t in range(m):
   assert (2**a*t)%target==0
   checks['finite_factor_transition']+=1
for i in range(8):
 for j in range(i,9):
  for z in range(-32,33):
   assert (z/2**i-2**(j-i)*z/2**j)==0
   checks['free_coordinate_transition']+=1
for k in range(9):
 m=2**k
 roots=[a for a in range(m) if 2*a%m==0]
 assert len(roots)<=2
 for a in roots:
  for b in roots:
   assert a==0 or b==0 or a==b
   checks['cyclic_involutions']+=1
for j in range(1,25):
 assert (2**(j-1))%(2**j)!=0
 checks['free_generator_nonzero']+=1
print(json.dumps({'status':'PASS','scope':'Exact finite quotient models of the retained transition maps; not Lean or global duality verification','checks':checks},indent=2))
