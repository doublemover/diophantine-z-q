from fractions import Fraction as F
import itertools,json,math
scales=0
for B,q,T in itertools.product([F(1,3),F(1),F(7,2),F(19)],range(1,21),[F(0),F(1,2),F(2),F(7)]):
 R=B/q
 assert R**5/R**6==q/B
 assert R**5/R**6*(2*T/B**2)==2*T*q/B**3
 assert R**5/R**6*(2*T/B**2)/B**3==2*T*q/B**6
 scales+=1
shells=0
for n in range(1,101):
 assert (2*n+1)**5-(2*n-1)**5==160*n**4+80*n*n+2
 shells+=1
# Exact canonical numerator/lift checks, including the unique unit of Z/1Z.
units=0
for q in range(1,65):
 for a in range(q):
  if math.gcd(a,q)==1:
   assert a%q==a
   assert any((a*b-1)%q==0 for b in range(q))
   units+=1
print(json.dumps({'status':'PASS','exact_five_six_dimensional_and_beta_scalings':scales,'rank_five_inverse_six_shell_identities':shells,'canonical_unit_numerator_checks':units,'scope':'Exact finite arithmetic/scaling regression only. Infinite summability, all-parameter Fourier bounds and actual error identities are supplied by the source/API chain, not these samples.'},indent=2))
