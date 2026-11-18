from itertools import product
# Orbit-stable pair labels at the U=W=0 nodes: (retained b, central V).
# At the second family: (b,V'=v/u,W'=w/u). Paired conics have no fixed points.
for e in product((1,-1), repeat=4):
 if e==(1,1,1,1): continue
 i=frozenset(j for j,x in enumerate(e) if x<0);b,u,v,w=e
 smooth=(8 if i in [frozenset([0]),frozenset([2]),frozenset(range(4))] else 0)
 swap_pts=0;curves=0
 for B,V in product((1,-1),repeat=2):
  if (B,V)!=(b*B,v*V): continue
  if u==w==-1:curves+=1
  elif u==-w:swap_pts+=2
  else:raise AssertionError('unexpected identity')
 for B,V,W in product((1,-1),repeat=3):
  if (B,V,W)==(b*B,v*u*V,w*u*W):
   assert u==v==w==-1;curves+=1
 assert smooth+swap_pts==(8 if len(i) in (1,4) else 0)
 assert curves==(4 if i=={1,3} else 8 if i=={1,2,3} else 0)
print('PASS 15 masks, 4+8 nodal labels, swap fixed points and whole invariant conics.')
