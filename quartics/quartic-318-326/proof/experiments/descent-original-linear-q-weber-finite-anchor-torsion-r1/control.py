import random
rng=random.Random(622403)
checked=0
for p in (3,5,7,11,13,17,19,23,29):
 q=p**6
 for k in range(1700):
  t=(p*rng.randrange(q//p))%q
  A=(p*rng.randrange(q//p))%q
  d=rng.randrange(q)
  w=0
  for _ in range(6): w=(t**3-t*w*w)%q
  assert (w+t*w*w-t**3)%q==0
  u=pow((1+t*w)%q,-1,q)
  beta=pow((1-A*t*t*u)%q,-1,q)
  B=t*d%q
  C=(2*d+(3*A*A-1)-(A**3+A)*t*t*u)%q
  H=(2*B+(3*A*A-1)*t-(A**3+A)*w)%q
  assert (t*C-H)%q==0
  Y=(-B+(1+B*w)*u*beta**3*H)%q
  e=(-d+(1+B*w)*u*beta**3*C)%q
  assert (Y-t*e)%q==0
  assert (e-d+1)%p==0
  checked+=1
print(f'{checked} exact lifted ordinate factorizations and signed residue decrements')
