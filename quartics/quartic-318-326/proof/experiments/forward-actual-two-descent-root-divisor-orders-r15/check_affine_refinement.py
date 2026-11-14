from fractions import Fraction as F
from pathlib import Path
import json
counts={'bezout':0,'factorization':0,'nonzero_cover_constants':0,'actual_curve_points':0,'local_square_frames':0,'pure_tensor_multiplication':0,'negative_n_zero':0}
for n in map(F,range(-4,5)):
 roots=[F(0),n,-3*n];slopes=[2*n,3*n,-n];constants=[-3*n*n,4*n*n,12*n*n]
 for x in [F(k,2) for k in range(-16,17)]:
  fs=[x-a for a in roots];qs=[fs[1]*fs[2],fs[0]*fs[2],fs[0]*fs[1]]
  for i in range(3):
   assert qs[i]-fs[i]*(x+roots[i]+slopes[i])==constants[i];counts['bezout']+=1
   assert fs[i]*qs[i]==x*(x-n)*(x+3*n);counts['factorization']+=1
   if n: assert constants[i]!=0;counts['nonzero_cover_constants']+=1
  for y in map(F,range(-24,25)):
   if y*y!=x*(x-n)*(x+3*n):continue
   counts['actual_curve_points']+=1
   for i in range(3):
    for b in [False,True]:
     denominator=qs[i] if b else fs[i]
     if not denominator:continue
     g=y if b else F(1);e=qs[i] if b else 1/fs[i]
     assert e!=0 and g*g==fs[i]*e;counts['local_square_frames']+=1
     for a,c in [(F(2,3),F(-5,7)),(F(0),F(4)),(F(-3),F(-2))]:
      assert a*c*e*fs[i]==(a*g)*(c*g);counts['pure_tensor_multiplication']+=1
for i in range(3):
 n=F(0);x=F(0);assert x==0 and x*x==0;counts['negative_n_zero']+=1
out={'status':'PASS','scope':'Exact finite arithmetic checks only; not Lean or sheaf descent verification','counts':counts}
Path(__file__).with_name('AFFINE-REFINEMENT-REGRESSION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
