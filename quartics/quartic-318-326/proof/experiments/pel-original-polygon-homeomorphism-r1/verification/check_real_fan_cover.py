#!/usr/bin/env python3
"""Exact rational Farkas certificates for all linear alternatives.
Static arithmetic supplement only; not a Lean or local-quotient-disk check.
"""
from pathlib import Path
from fractions import Fraction as Q
import ast,re,itertools,json
P=Path(__file__).resolve().parent.parent
def table(mod,name):
 s=(P/(mod+'.lean')).read_text();a=s.index('def '+name+' ');a=s.index('![',a);b=s.index('\n',a)
 text=s[a:b].replace('![','[')
 def go(n):
  if isinstance(n,ast.Constant):return Q(n.value)
  if isinstance(n,(ast.List,ast.Tuple)):return [go(x) for x in n.elts]
  if isinstance(n,ast.UnaryOp):return -go(n.operand)
  if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div):return go(n.left)/go(n.right)
  raise ValueError(ast.dump(n))
 return go(ast.parse(text,mode='eval').body)
F='PELDirichletVertexFan318';C='PELDirichletVertexCycles318'
rays=table(F,'ray');ori=table(F,'orientation');cl=list(map(int,table(C,'vertexClass')));nxt=list(map(int,table(C,'nextVertex')))
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def cert(normals):
 for a in normals:
  if a==(0,0):return True
 for a,b in itertools.combinations(normals,2):
  if cross(a,b)==0 and a[0]*b[0]+a[1]*b[1]<0:return True
 for a,b,c in itertools.combinations(normals,3):
  weights=[cross(b,c),cross(c,a),cross(a,b)]
  if (all(w>=0 for w in weights) and any(w>0 for w in weights)) or (all(w<=0 for w in weights) and any(w<0 for w in weights)):return True
 return False
counts=[]
for i in range(5):
 vs=[v for v in range(28) if cl[v]==i]
 pairs=[]
 for v in vs:
  a,b=rays[v],rays[nxt[v]];o=ori[i]
  assert o*cross(a,b)>0
  pairs.append([(-o*a[1],o*a[0]),(o*b[1],-o*b[0])])
 branches=list(itertools.product(*pairs))
 assert all(cert(branch) for branch in branches),(i,'uncovered real direction')
 counts.append(len(branches))
print(json.dumps({'status':'PASS','all_strict_complement_systems_infeasible':counts,'total':sum(counts),'scope':'Exact all-real linear fan cover arithmetic; no quotient disk or Lean certification'}))
