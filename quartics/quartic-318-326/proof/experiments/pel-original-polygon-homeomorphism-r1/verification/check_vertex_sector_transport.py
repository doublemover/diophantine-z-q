import runpy,json
from pathlib import Path
from fractions import Fraction as Q
P=Path(__file__).resolve().parent
a=runpy.run_path(str(P/'check_side_pairings.py'))
d=json.loads((P/'second-ray-tables.json').read_text())
vs=a['vs'];ori=a['orient'];cl=a['cl'];other=a['other'];cross=a['cross']
for key in ['previousVertex','secondEndpoint','secondRayScale']:
 assert a['table']('PELOriginalSecondVertexRay318',key)==list(map(Q,d[key]))
for vv in range(28):
 mm=a['mat'](a['bar'](a['prefix'][vv]));w=a['homogeneous'](a['bar'](a['prefix'][vv]),vs[vv])
 direction=[vs[d['secondEndpoint'][vv]][k]-vs[vv][k] for k in range(2)]
 dv=mm*a['S'].Matrix([*direction,0])
 tangent=[(dv[k]*w[2]-w[k]*dv[2])/w[2]**2 for k in range(2)]
 assert tangent==[Q(d['secondRayScale'][vv])*a['rays'][d['previousVertex'][vv]][k] for k in range(2)]
constants=[Q(n) for n in [672,222,8232,980,4200,1125,222,5]]
first=list(map(Q,['104/5','34/5','1204/5','28','116','30','26/5','0']))
second=list(map(Q,['0','18','1176','168','840','255','66','3']))
def positive_multiple(x,y):
 return cross(x,y)==0 and sum(u*v for u,v in zip(x,y))>0
for v in range(28):
 A=tuple(vs[other[v]][k]-vs[v][k] for k in range(2))
 B=tuple(vs[d['secondEndpoint'][v]][k]-vs[v][k] for k in range(2))
 o=ori[cl[v]];assert o*cross(B,A)>0
 # Active-row inequalities are n dot W <= 0. Sector inequalities are -m dot W <= 0.
 sector_normals=[(o*B[1],-o*B[0]),(-o*A[1],o*A[0])]
 active=set()
 for j in range(8):
  for eps in [-1,1]:
   for delta in [-1,1]:
    n=(first[j]*eps,second[j]*delta)
    if sum(n[k]*vs[v][k] for k in range(2))==constants[j]:active.add(n)
 assert len(active)==2,(v,active)
 assert all(any(positive_multiple(n,m) for m in sector_normals) for n in active)
 assert all(any(positive_multiple(n,m) for n in active) for m in sector_normals)
print('PASS: all28 full active cones equal signed sectors between second and first incident edges; all active signed rows covered.')

import sympy as S
aa,bb,cc,dd,ee,ff,x,y,u,v=S.symbols('a b c d e f x y u v')
NP=aa*x+bb*y+cc;NQ=aa*u+bb*v+cc;DP=dd*x+ee*y+ff;DQ=dd*u+ee*v+ff
L=aa*(u-x)+bb*(v-y);LD=dd*(u-x)+ee*(v-y)
assert S.factor(NQ/DQ-NP/DP-(DP/DQ)*(L*DP-NP*LD)/DP**2)==0
print('PASS: exact generic projective displacement factor DP/DQ; this is symbolic arithmetic, not Lean or local quotient topology.')
