import json
c=dict(nontrivial_actions=0,crossed_cocycles=0,power_levels=0,kummer_kernel=0,full_kernel=0,actual_division_lifts=0)
for j in range(1,8):
 N=2**j
 for a in range(N):
  if a*a%N!=1:continue
  if a!=1:c['nontrivial_actions']+=1
  fixed={x for x in range(N) if (a-1)*x%N==0}
  Z={z for z in range(N) if (a+1)*z%N==0}
  B={(a-1)*x%N for x in range(N)}
  assert B<=Z;c['crossed_cocycles']+=len(Z)
  for k in range(j+1):
   M=2**k;T={x for x in range(N) if M*x%N==0};ZT=Z&T;BT={(a-1)*x%N for x in T}
   assert BT<=ZT;c['power_levels']+=1
   connecting={(a-1)*q%N for q in range(N) if M*q%N in fixed}
   assert connecting==ZT&B;c['full_kernel']+=len(ZT)
   fixedmultiples={M*x%N for x in fixed}
   for q in range(N):
    P=M*q%N
    if P not in fixed:continue
    assert (((a-1)*q%N in BT)==(P in fixedmultiples));c['kummer_kernel']+=1
   for R in range(N):
    Q=M*R%N
    for z in Z:
     if M*z%N!=(a-1)*Q%N:continue
     w=(z-(a-1)*R)%N
     assert w in ZT and (z-w)%N in B;c['actual_division_lifts']+=1
print(json.dumps({'status':'PASS','counts':c},indent=2))
