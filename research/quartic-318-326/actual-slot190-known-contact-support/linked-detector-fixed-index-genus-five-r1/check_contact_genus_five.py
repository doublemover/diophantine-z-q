#!/usr/bin/env python3
"""Exact fixed branch/quotient arithmetic; no variable h or rational points searched."""
from fractions import Fraction as F
from itertools import combinations
import json
a=[(1,0),(2,1),(1,1),(2399,-1),(407,32)]
r=[F(-v,u) for u,v in a]
assert r==[F(0),-F(1,2),-F(1),F(1,2399),-F(32,407)]
dets=[(i,j,a[i][0]*a[j][1]-a[j][0]*a[i][1]) for i,j in combinations(range(5),2)]
assert [u[2] for u in dets]==[1,1,-1,32,1,-2401,-343,-2400,-375,77175]
def bp(v):
    return ([0] if v.bit_count()%2 else [])+[i+1 for i in range(4) if (v>>i)&1]
assert {v:len(bp(v)) for v in range(1,16)}.values()
assert sorted(len(bp(v)) for v in range(1,16))==[2]*10+[4]*5
quot=[]
for v in range(1,16):
    b=bp(v)
    if len(b)==2:continue
    A,B,C,D=(r[j] for j in b)
    l=(C-A)*(D-B)/((C-B)*(D-A))
    j=256*(1-l+l*l)**3/(l*l*(1-l)**2)
    quot.append([v,b,str(l),str(j)])
assert [q[2] for q in quot]==['2401','-343/32','-1/224','-5/1024','35/32']
assert (-2*16+5*8+2)//2==5
print(json.dumps(dict(actual_root_values=list(map(str,r)),determinants=dets,
                      degree=16,branch_points=5,ramification_index=2,
                      genus=5,four_branch_quotients=quot),indent=2))
