from fractions import Fraction as F
count=0
for u in range(-8,9):
 for v in range(-7,8):
  if not v: continue
  for a in range(-6,7):
   U,V,A=map(F,(u,v,a));x=U/V
   assert x*V==U
   assert (x-A)*V==U-A*V
   assert x-A==(U-A*V)/V
   count+=1
assert (F(2)/3-5)*3 != 2+5*3
assert (F(2)/3-5)*3 != 2-5/3
print('PASS exact overlap/root identities:',count,'negative controls: 2')
