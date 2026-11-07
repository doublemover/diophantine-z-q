"""Generate an exact degree-four theorem from the an isolated pure-square gate."""
from pathlib import Path
import json,sys
folder=Path(sys.argv[1]);module=sys.argv[2];out=Path(sys.argv[3]);ns=out.stem
ir=json.loads((folder/'compiled-ir.json').read_text());cm=json.loads((folder/'coordinate-map.json').read_text());mp={e['sourceId']:e['compactId'] for e in cm['mapping']};n=len(mp)
from fractions import Fraction
from collections import defaultdict
occ=defaultdict(list)
for k,r in enumerate(ir['residuals']):
 for v in {v for t in r['terms'] for v in t['monomial']}:occ[v].append(k)
candidates=[]
for v,ks in occ.items():
 if len(ks)!=1:continue
 idx=ks[0];row=ir['residuals'][idx]
 if len(row['terms'])!=2:continue
 quad=next((t for t in row['terms'] if t['monomial']==[v,v] and Fraction(t['coefficient'])==1 and t.get('sPower',0)==0),None)
 if quad is None:continue
 other=next(t for t in row['terms'] if t is not quad)
 if Fraction(other['coefficient'])!=-1 or other.get('sPower',0)!=0 or len(other['monomial'])!=1 or other['monomial'][0]==v:continue
 candidates.append((v,idx,row,other))
assert candidates,'No isolated pure-square pivot for the exact-degree proof'
v,idx,row,other=min(candidates)
i=mp[v];j=mp[other['monomial'][0]];assert i!=j
before='['+', '.join(module+'.row'+str(k) for k in range(idx))+']'
after='['+', '.join(module+'.row'+str(k) for k in range(idx+1,len(ir['residuals'])))+']'
s=f'''module
public import {module}
public import ExactDegree
public section
namespace {ns}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def before : List (List (SparseQuartic.Term {n})) := {before}
def after : List (List (SparseQuartic.Term {n})) := {after}

theorem degree_exactly_four : {module}.P.totalDegree = 4 := by
  change (SparseQuartic.polynomial {module}.scale
    (before ++ {module}.row{idx} :: after)).totalDegree = 4
  apply ExactDegree.degree_exactly_four {module}.scale ({i} : Fin {n}) {j} (by decide)
    before after {module}.row{idx}
  · simp [SparseQuartic.residualPolynomial, SparseQuartic.termPolynomial,
      SparseQuartic.monomialPolynomial, {module}.row{idx}]
    ring
  · decide

end {ns}
'''
out.write_text(s);print({'coordinates':n,'squarePivotRow':idx,'pivotCoordinate':i,'otherCoordinate':j})
