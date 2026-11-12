from itertools import product
import json
c=dict(actual_restrictions=0,local_image_comparisons=0,all_place_intersections=0,primary_levels=0)
for j in range(1,7):
 N=2**j
 for a in range(N):
  if a*a%N!=1:continue
  Z={z for z in range(N) if (a+1)*z%N==0};B={(a-1)*q%N for q in range(N)}
  for k in range(j+1):
   M=2**k;T={q for q in range(N) if M*q%N==0};ZT=Z&T;BT={(a-1)*q%N for q in T}
   K={(a-1)*q%N for q in range(N) if (a-1)*M*q%N==0}
   assert K==ZT&B;c['local_image_comparisons']+=1
   for u in range(min(N,12)):
    assert {u*z%N for z in ZT}<=ZT
    assert {u*b%N for b in BT}<=BT
    c['actual_restrictions']+=1
   for us in [(1,2,3),(2,4,6),(0,1,7)]:
    S={z for z in ZT if all(u*z%N in K for u in us)}
    pre={z for z in ZT if all(u*z%N in B for u in us)}
    assert S==pre and BT<=S
    c['all_place_intersections']+=1
for j in range(10):
 for k in range(10):
  N=2**j
  killed={x for x in range(N) if 2**k*x%N==0}
  assert len(killed)==2**min(j,k)
  c['primary_levels']+=1
print(json.dumps({'status':'PASS','counts':c},indent=2))
