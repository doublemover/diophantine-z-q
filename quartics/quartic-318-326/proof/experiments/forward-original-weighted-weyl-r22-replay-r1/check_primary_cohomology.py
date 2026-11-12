import json
c=dict(uniform_primary_images=0,eventual_boundaries=0,directed_relations=0,selmer_levels=0)
for j in range(1,8):
 N=2**j
 for a in range(N):
  if a*a%N!=1:continue
  Z={z for z in range(N) if (a+1)*z%N==0};B={(a-1)*t%N for t in range(N)}
  for z in Z:
   ks=[k for k in range(j+1) if 2**k*z%N==0]
   assert ks;c['uniform_primary_images']+=1
   if z in B:
    t=next(t for t in range(N) if (a-1)*t%N==z)
    k=next(k for k in range(j+1) if 2**k*t%N==0)
    assert z in {(a-1)*u%N for u in range(N) if 2**k*u%N==0};c['eventual_boundaries']+=1
  for i in range(j+1):
   Zi={z for z in Z if 2**i*z%N==0}
   for k in range(i,j+1):
    Zk={z for z in Z if 2**k*z%N==0}
    assert Zi<=Zk;c['directed_relations']+=1
   for us in [(1,2),(0,3),(2,4)]:
    S={z for z in Zi if all(u*z%N in B for u in us)}
    assert S=={z for z in Z if 2**i*z%N==0 and all(u*z%N in B for u in us)}
    c['selmer_levels']+=1
print(json.dumps({'status':'PASS','counts':c},indent=2))
