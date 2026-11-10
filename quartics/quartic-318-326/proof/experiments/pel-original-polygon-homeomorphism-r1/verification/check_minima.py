#!/usr/bin/env python3
"""Exact all-vertex energy, exhaustive reduced boxes and closed strip checks.
Does not run Lean or certify any topological fundamental-domain theorem.
"""
from pathlib import Path
import runpy,itertools,json
D=runpy.run_path(str(Path(__file__).with_name('check_side_pairings.py')))
S=D['S'];table=D['table'];vs=D['vs'];inv=table('PELOriginalVertexEnergy318','inverseMatrix');fwd=table('PELOriginalVertexEnergy318','forwardMatrix');kind=list(map(int,table('PELOriginalVertexEnergy318','kind')))
x=S.Matrix(S.symbols('a b c d'));r=x[0]+x[2]/2;i=x[1]+x[3]/2;j=x[2]/2;k=x[3]/10
N=r*r+210*i*i-5*j*j-1050*k*k
bn=lambda a,b:a*a-a*b-b*b
be=lambda a,b:2*a*a-2*a*b+3*b*b
def norms(a,b,c,d):return [6*bn(a,c)-7*bn(b,d),-2*bn(a,b)+21*bn(c,d),3*bn(a,b)-14*bn(c,d),-3*bn(a,b)+14*bn(c,d),2*bn(a,b)-21*bn(c,d)]
def energies(a,b,c,d):return [6*be(a,c)+7*be(b,d),2*be(a,b)+21*be(c,d),3*be(a,b)+14*be(c,d),3*be(a,b)+14*be(c,d),2*be(a,b)+21*be(c,d)]
thresholds=list(map(int,table('IntegralBinaryEnergy318','threshold')))
for v in range(28):
 I=S.Matrix(inv[v]);F=S.Matrix(fwd[v]);assert I*F==S.eye(4) and F*I==S.eye(4)
 args=I*x
 den=2*(r*k-i*j)*vs[v][0]+2*(r*j+210*i*k)*vs[v][1]+r*r+210*i*i+5*j*j+1050*k*k
 assert S.expand(norms(*args)[kind[v]]-N)==0,(v,'norm')
 assert S.expand(energies(*args)[kind[v]]-thresholds[kind[v]]*den)==0,(v,'energy')
boxes=[(2,2,1,1),(7,5,2,1),(4,3,2,1),(4,3,2,1),(6,4,2,1)]
weights=[(6,7,12,14),(2,4,21,42),(3,6,14,28),(3,6,14,28),(2,4,21,42)]
box_rows=[]
for t,box in enumerate(boxes):
 # The positive-square lower estimate forces these coordinate bounds for
 # every energy strictly below the threshold, not just sampled points.
 assert all(w*(b+1)**2>=thresholds[t] for w,b in zip(weights[t],box))
 es=[energies(*z)[t] for z in itertools.product(*(range(-b,b+1) for b in box)) if norms(*z)[t]==1]
 assert min(es)==thresholds[t]
 box_rows.append({'kind':t,'threshold':thresholds[t],'box':box,'minimum':min(es),'minimizers':es.count(min(es))})
# 13 exact horizontal closed strips exhaust the polygon's full y range.
rows=D['table']('PELDirichletOriginalUnits318','rowConstant');xs=D['table']('PELDirichletOriginalUnits318','rowFirst');ys=D['table']('PELDirichletOriginalUnits318','rowSecond')
js=[6,5,4,3,2,1,0,1,2,3,4,5,6]
for n,jj in enumerate(js):
 lo=vs[2*n][1];hi=vs[2*n+2][1];assert lo<hi
 m=(-1 if n>=6 else 1)*ys[jj]/xs[jj];t=rows[jj]/xs[jj]
 assert vs[2*n]==[-(m*lo+t),lo] and vs[2*n+1]==[m*lo+t,lo]
 assert vs[2*n+2]==[-(m*hi+t),hi] and vs[2*n+3]==[m*hi+t,hi]
assert vs[0][1]==-S.Rational(5,3) and vs[-1][1]==S.Rational(5,3)
# Independent second-ray transport: local cone v maps to sector(previous v),
# not sector v. Save full exact tables for the analytic worker.
prev=[];other=[];scales=[]
for v in range(28):
 ends={D['end'][e] if D['start'][e]==v else D['start'][e] for e in range(28) if v in [D['start'][e],D['end'][e]]};w,=ends-{D['other'][v]}
 z=D['nxt'].index(v);M=D['mat'](D['bar'](D['prefix'][v]));H=D['homogeneous'](D['bar'](D['prefix'][v]),vs[v]);dv=M*S.Matrix([vs[w][0]-vs[v][0],vs[w][1]-vs[v][1],0]);t=[(dv[a]*H[2]-H[a]*dv[2])/H[2]**2 for a in range(2)];ray=D['rays'][z];ix=0 if ray[0] else 1;scale=t[ix]/ray[ix]
 assert scale>0 and all(t[a]==scale*ray[a] for a in range(2)),(v,z)
 prev.append(z);other.append(w);scales.append(str(scale))
result={'scope':'exact rational/symbolic check, not Lean kernel or topology','boxes':box_rows,'previousVertex':prev,'secondEndpoint':other,'secondRayScale':scales}
Path(__file__).with_name('MINIMA-AND-SECOND-RAY.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: all 28 exact energy identities, all five exhaustive reduced norm-one boxes, all 13 closed polygon strips, all 28 positive previous-sector second rays.')
