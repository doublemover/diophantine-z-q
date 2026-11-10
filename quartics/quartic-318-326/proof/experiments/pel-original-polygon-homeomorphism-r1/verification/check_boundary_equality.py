#!/usr/bin/env python3
"""Exhaustive exact boundary equality classification, separate from Lean checking."""
from pathlib import Path
import runpy,itertools
D=runpy.run_path(str(Path(__file__).with_name('check_minima.py')));A=D['D'];S=D['S']
M=A['table']('IntegralBinaryEnergyMinimizers318','minimizer');im=A['table']('PELOriginalVertexEquality318','imageVertex')
for j,box in enumerate(D['boxes']):
 assert all(w*(b+1)**2>D['thresholds'][j]for w,b in zip(D['weights'][j],box))
 expected={z for z in itertools.product(*(range(-b,b+1)for b in box))if D['norms'](*z)[j]==1 and D['energies'](*z)[j]==D['thresholds'][j]}
 assert {tuple(z)for z in M[j]}==expected
allunits=[]
for v in range(28):
 us=[tuple(S.Matrix(D['fwd'][v])*S.Matrix(z))for z in M[D['kind'][v]]];allunits.append(set(us))
 for k,u in enumerate(us):
  w=int(im[v][k]);assert A['act'](u,A['vs'][v])==A['vs'][w];assert A['cl'][v]==A['cl'][w]
one=(1,0,0,0);neg=lambda x:tuple(-z for z in x)
for e in range(28):
 actual=allunits[A['start'][e]]&allunits[A['end'][e]]
 want={one,neg(one),tuple(A['units'][e]),neg(A['units'][e])}
 assert actual==want,(e,actual,want)
print('PASS exact complete5 reduced equality lists, all448 vertex images/classes, all28 endpoint intersections exactly +/-1,+/- original edge unit. Not Lean or global quotient validation.')
