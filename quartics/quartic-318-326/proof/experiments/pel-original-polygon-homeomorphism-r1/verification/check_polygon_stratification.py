#!/usr/bin/env python3
"""Exact original signed-side and whole-side parameter checks; no Lean invocation."""
from pathlib import Path
import runpy,itertools
from fractions import Fraction as Q
P=Path(__file__).resolve().parent
a=runpy.run_path(str(P/'check_side_pairings.py'))
vs,rows,start,finish=a['vs'],a['rows'],a['start'],a['end']
const=list(map(Q,['672','222','8232','980','4200','1125','222','5']))
first=list(map(Q,['104/5','34/5','1204/5','28','116','30','26/5','0']))
second=list(map(Q,['0','18','1176','168','840','255','66','3']))
ns=a['table']('PELOriginalPolygonBoundary318','startNeighbor');nf=a['table']('PELOriginalPolygonBoundary318','finishNeighbor')
for j,eps,delta in itertools.product(range(8),[1,-1],[1,-1]):assert [const[j],-first[j]*eps,-second[j]*delta] in rows
for e in range(28):
 A,B=vs[start[e]],vs[finish[e]];D=[B[k]-A[k] for k in range(2)]
 assert D!=[0,0]
 def value(row,P):return row[0]+row[1]*P[0]+row[2]*P[1]
 assert value(rows[e],A)==value(rows[e],B)==0
 srow,frow=rows[int(ns[e])],rows[int(nf[e])]
 assert value(srow,A)==0 and value(srow,B)>0
 assert value(frow,B)==0 and value(frow,A)>0
 # Along the full affine line P=A+sD, start-neighbor = positive*s,
 # finish-neighbor = positive*(1-s), giving exactly0<=s<=1.
 assert sum(srow[k+1]*D[k] for k in range(2))==value(srow,B)
 assert sum(frow[k+1]*D[k] for k in range(2))==-value(frow,A)
print('PASS: all32 signed rows represented; all28 nondegenerate whole edge lines, exact positive neighboring bounds and endpoint parameters. No topological cellulation or Lean claim.')
