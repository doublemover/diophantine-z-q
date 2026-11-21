from pathlib import Path
import json
import sys
D=Path(sys.argv[1])
d=json.loads((D/'EXACT-VARIABLE-SHIFT-2887.json').read_text())
s=json.loads((D.parent/'ct-original-scalar-kummer-fiber-r1'/'PINNED-SCALAR-FIBER.json').read_text())
p=d['p'];m=p*p;h,J,R,N=(s[k] for k in ('h','J','R_input','N'))
assert N==65536
beta=d['beta']; assert 144*17*beta==114444*R
assert d['variable_local_input_mod_p2']==[[2805,1171715],[2181,4062213]]
Hsq=[];Usq=[];P0sq=[]
for root,Q0 in zip((d['sqrt2_mod_p2'],-d['sqrt2_mod_p2']),d['variable_local_input_mod_p2']):
 a=-(3-root)**2 % m
 assert root*root%m==2
 vals=lambda k:(k**3+a*k)%p
 squares={i*i%p for i in range(1,p)}
 order=1+sum(1 if vals(k)==0 else 2 if vals(k) in squares else 0 for k in range(p))
 assert order==2888
 Q=(*(x%m for x in Q0),1);P=(1+root,2*root,1)
 O=(1,1,0)
 def red(X,Y,Z):
  X%=m;Y%=m;Z%=m
  assert any(u%p for u in (X,Y,Z)),(X,Y,Z)
  assert (Y*Y-X**3-a*X*Z**4)%m==0
  return X,Y,Z
 def twice(P):
  X,Y,Z=P
  if not Z:return O
  S=4*X*Y**2; M=3*X**2+a*Z**4
  XX=M*M-2*S
  return red(XX,M*(S-XX)-8*Y**4,2*Y*Z)
 def add(P,Q):
  X,Y,Z=P; x,y,z=Q
  if Z==0:return Q
  if z==0:return P
  U=X*z*z; V=x*Z*Z; A=Y*z**3; B=y*Z**3
  h=(V-U)%m; r=(B-A)%m
  if not h and not r:return twice(P)
  assert h%p or r%p,("degenerate",P,Q)
  h2=h*h%m; h3=h*h2%m
  XX=r*r-h3-2*U*h2
  return red(XX,r*(U*h2-XX)-A*h3,h*Z*z)
 def mult(P,n):
  Q=O
  for b in bin(n)[2:]:
   Q=twice(Q)
   if b=='1':Q=add(Q,P)
  return Q
 def sqU(P):
  X,Y,Z=P
  # Compute original U=2y/(x*x-a) directly from the second weighted
  # projective coordinate, not from the shifted x([2]Q) formula.
  U=2*Y*Z*pow((X*X-a*Z**4)%m,-1,m)%m
  return U*U %m
 j=(pow(6,15,order*p)*pow(3,N,order*p)*J)%(order*p)
 Hsq.append(sqU(mult(P,h%(order*p))));Usq.append(sqU(mult(Q,j)));P0sq.append(sqU(mult(P,j)))
H2=Hsq[0]*Hsq[1]%m; inv=pow(R,-1,m)
N0=(1+H2*inv*inv+(Hsq[0]+Hsq[1])*inv)%m
Q2=Usq[0]*Usq[1]*pow(H2,-1,m)*pow(inv,30,m)%m
W=(N0*N0+R*Q2)%m
c=12*W*pow(1+114444*R,-1,m)%m
delta=(1-beta*c*c)%m
assert (H2,N0,Q2,W,c,delta)==tuple(d['variable_fold_mod_p2'][k] for k in ['H2','Npack','Q2','W','c','delta'])
assert (H2,N0,Q2,W,c,delta)==(5700095,5326656,1518240,2019080,639243,392632)
P0Q2=P0sq[0]*P0sq[1]*pow(H2,-1,m)*pow(inv,30,m)%m
P0c=12*(N0*N0+R*P0Q2)*pow(1+114444*R,-1,m)%m
assert (1-beta*P0c*P0c)%p==1634
print((H2,N0,Q2,W,c,delta),delta//p,'original_P0_unit',1634)
