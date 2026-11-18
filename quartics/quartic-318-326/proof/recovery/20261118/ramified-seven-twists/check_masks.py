# Exact elementary mask enumeration, complement of the geometric proof.
from itertools import product
for e in product((-1,1),repeat=4):
 if e==(1,1,1,1):continue
 a,b,c,d=e; I={i for i,v in enumerate(e) if v==-1}
 outside=8*int(I=={1} or len(I)==4)
 # On the U-chart with t != 0 a fixed point requires stable j,b,t.
 middle=8*int(b==1 and a*c==1 and -a==1 and a*d==-1)
 # Third conic has four b,tau labels. At w!=0 exactly one of its two
 # remaining projective directions flips -> two isolated points per conic.
 terminal=8*int(b==1 and -d==1 and a!=c)
 isolated=outside+middle+terminal
 assert isolated==(8 if I in [{1},{0,1,2,3},{0,2},{0,3},{2,3}] else 0)
 # First 8 X*Y=7 nodes: all or none stabilize, and never swapped branches.
 stable_first=sum((B,J,H)==(b*B,a*c*J,a*d*H) for B,J,H in product((1,-1),repeat=3))
 assert stable_first==(8 if I=={0,2,3} else 0)
print('PASS 15 sign masks; middle normalization labels, conic reflections, fixed ends.')
