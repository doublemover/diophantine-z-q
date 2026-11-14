#!/usr/bin/env python3
"""Exact all-order paired/diagonal/scaled difference identities. Polynomial finite model, not compact-smooth existence or Lean validation."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import json
add=lambda x,y:tuple(a+b for a,b in zip(x,y))
scale=lambda x,B:tuple(F(a)/B for a in x)
norm=lambda x:max(map(abs,x),default=F(0))
def W(x):
 z=F(1)
 for a in x:z*=1+a+a*a
 return z

def mixed(f,us,x):
 if not us:return f(x)
 return mixed(f,us[1:],add(x,us[0]))-mixed(f,us[1:],x)
def prodnorm(us):
 z=F(1)
 for u in us:z*=norm(u)
 return z

def run():
 counts=dict(paired_diagonal_all_orders=0,scaled_actual_pair_identity=0,exact_direction_scaling=0,unit_direction_lists=0,zero_step_annihilation=0,negative_controls=0)
 dirs=[tuple(F(i==j) for i in range(5)) for j in range(5)]
 zero=(F(0),)*5
 lists=[]
 for k in range(6):
  lists += [tuple(dirs[i] for i in ss) for ss in combinations(range(5),k)]
  if k:lists += [tuple([dirs[0]]*k),tuple([zero]*k),tuple([tuple(-a for a in dirs[1])]*k)]
 bases=[zero,(F(1,2),F(-1,3),0,1,-1)]
 shifts=[zero,(1,-1,2,0,F(1,3))]
 for us,x,h in product(lists,bases,shifts):
  P=lambda z:W(add(z,h))*W(z)
  D=lambda p:W(p[:5])*W(p[5:])
  diagonal=tuple(u+u for u in us)
  assert mixed(P,us,x)==mixed(D,diagonal,add(x,h)+tuple(x))
  assert prodnorm(diagonal)==prodnorm(us)
  counts['paired_diagonal_all_orders']+=1
  assert prodnorm(us)<=1
  counts['unit_direction_lists']+=1
  if us and any(u==zero for u in us):
   assert mixed(P,us,x)==0;counts['zero_step_annihilation']+=1
  for B in (F(1),F(2),F(5,2)):
   usB=tuple(scale(u,B) for u in us)
   lattice=lambda z:W(scale(add(h,z),B))*W(scale(z,B))
   shifted=lambda y:W(add(y,scale(h,B)))*W(y)
   assert mixed(lattice,us,x)==mixed(shifted,usB,scale(x,B))
   counts['scaled_actual_pair_identity']+=1
   assert prodnorm(usB)==B**(-len(us))*prodnorm(us)
   counts['exact_direction_scaling']+=1
 # Order0 must retain amplitude; translated factor cannot be silently frozen.
 assert mixed(lambda z:W(z)**2,(),zero)==1
 assert mixed(lambda z:W(add(z,dirs[0]))*W(z),(dirs[0],),zero)!=mixed(lambda z:W(dirs[0])*W(z),(dirs[0],),zero)
 # Two independent step scalings are not one, and product max norm is not sum norm.
 assert prodnorm((scale(dirs[0],2),scale(dirs[1],2)))!=F(1,2)
 assert norm(dirs[0]+dirs[0])!=2*norm(dirs[0])
 counts['negative_controls']=4
 return {'status':'PASS','scope':'Exact finite all-order algebra and positive scaling on a polynomial model; NOT compact support, C-infinity derivative existence, global norm estimates, Lean elaboration or minor-arc saving.','counts':counts}
if __name__=='__main__':
 result=run();Path(__file__).with_name('ALL-DIFFERENCE-ORDERS-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
