from itertools import product
for e in product((1,-1),repeat=4):
 if e==(1,1,1,1):continue
 b,u,v,w=e;I={i for i,s in enumerate(e) if s<0}
 outside=8*int(I=={0} or len(I)==4)
 smooth=8*int(b==1 and -v==-w==1 and -u==-1)
 swap=0;fixed_conic=0;fixed_ends=0
 for B,U in product((1,-1),repeat=2):
  if (B,U)!=(b*B,-u*U):continue
  if v!=w:swap+=2
  elif v==1:fixed_conic+=1
  else:fixed_ends+=2
 assert outside+smooth+swap==(8 if I in [{0},{0,1,2,3},{2,3},{1,2},{1,3}] else 0)
 assert fixed_conic==(4 if I=={1} else 0) and fixed_ends==(8 if I=={1,2,3} else 0)
assert 76800==25600*3 and 375==125*3 and 125+25600==8575*3
print('PASS: scaling/cluster constants, all fifteen masks and the two endpoint types.')
