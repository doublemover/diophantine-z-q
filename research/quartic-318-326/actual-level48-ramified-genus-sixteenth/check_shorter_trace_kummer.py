#!/usr/bin/env python3
"""Finite signed support checks for shorter unselected comparison twists."""
import itertools,json
R={}
def sy(a,p):return 1 if pow(a%p,(p-1)//2,p)==1 else -1
# Representative q0=7, old helper r=97 (17/r)=-, with same required local characters.
assert [sy(d,7) for d in (-1,2,3)]==[-1,1,-1]
r=97
assert [sy(d,r) for d in (-1,2,3,17)]==[1,1,1,-1]
S=[[(-1)**t*2**i*3**j*17**k,t,i,j,k] for t,i,j,k in itertools.product(range(2),repeat=4)]
A=[d for d in S if d[1]==0 and sy(d[0],r)==1 and sy(d[0],7)==1]
B=[d for d in S if sy(d[0],r)==1 and sy(d[0],7)==1 and d[3]==0 and (d[0]%3)==1]
# Actual global second at 3 must be a square class; the Q3-unit check also excludes 2,
# so the array with just valuation requirement records weakest sufficient short table.
Bweak=[d for d in S if sy(d[0],r)==1 and sy(d[0],7)==1 and d[3]==0]
assert [a[0] for a in A]==[1,2] and [b[0] for b in Bweak]==[1,2]
assert [b[0] for b in B]==[1]
R['first_after_old_helper_q0']=sorted(x[0] for x in A);R['second_weak_after_3']=sorted(x[0] for x in Bweak)
R['second_using_full_3_square']=sorted(x[0] for x in B)
R['odd_valuation1_unit_pairs']=sorted([(u,(u+2*n)%8) for n in (7,) for u in (1,3,5,7)])
assert (1,1) not in R['odd_valuation1_unit_pairs']
print(json.dumps(R,sort_keys=True))
