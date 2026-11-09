#!/usr/bin/env python3
from pathlib import Path
import runpy
import sympy as s
P=Path(__file__).resolve().parents[1]
f=runpy.run_path(str(P/'verification/check_reduction.py'))
a=runpy.run_path(str(P/'verification/check_normalizers.py'))
V,mul,red,mod=f['V'],f['mul'],f['red'],f['mod'];N=a['N'];omul,bar=a['mul'],a['bar']
F=[[[1,0,0,0],[0,0,1,1],[0,0,1,0],[0,2,1,0]],[[1,0,0,0],[0,1,2,0],[0,0,2,0],[0,0,1,2]],[[1,0,0,0],[0,0,0,2],[0,0,1,0],[0,1,0,0]],[[1,0,0,0],[0,2,0,0],[0,0,1,0],[0,0,2,2]]]
B=[[[1,0,0,0],[0,0,1,2],[0,0,1,0],[0,1,2,0]],[[1,0,0,0],[0,1,2,0],[0,0,2,0],[0,0,2,2]],[[1,0,0,0],[0,0,0,1],[0,0,1,0],[0,2,0,0]],[[1,0,0,0],[0,2,0,0],[0,0,1,0],[0,0,2,2]]]
t=(P/'PELNormalizerReductionAction318.lean').read_text()
for row in ['⟨x.re,x.imJ+x.imK,x.imJ,2*x.imI+x.imJ⟩','⟨x.re,x.imI+2*x.imJ,2*x.imJ,x.imJ+2*x.imK⟩','⟨x.re,2*x.imK,x.imJ,x.imI⟩','⟨x.re,2*x.imI,x.imJ,2*x.imJ+2*x.imK⟩','⟨x.re,x.imJ+2*x.imK,x.imJ,x.imI+2*x.imJ⟩','⟨x.re,x.imI+2*x.imJ,2*x.imJ,2*x.imJ+2*x.imK⟩','⟨x.re,x.imK,x.imJ,2*x.imI⟩']:assert row in t
act=lambda i,x:mod(s.Matrix(F[i])*s.Matrix(x))
back=lambda i,x:mod(s.Matrix(B[i])*s.Matrix(x))
for i,(p,n) in enumerate(N):
 sq=tuple(z//p for z in omul(n,n));sqinv=bar(sq)
 for x in V:
  assert back(i,act(i,x))==act(i,back(i,x))==x
  # Entire original reduction/conjugation square.
  original=tuple(z//p for z in omul(omul(n,x),bar(n)))
  assert act(i,red(x))==red(original)
  assert act(i,act(i,x))==mul(mul(red(sq),x),red(sqinv))
  rx=(x[0],x[2]);ax=act(i,x)
  assert (ax[0],ax[2])==(rx[0],(-rx[1])%3) if i==1 else (ax[0],ax[2])==rx
  for y in V:assert act(i,mul(x,y))==mul(act(i,x),act(i,y))
 for j,(q,m) in enumerate(N):
  c=tuple(z//(p*q) for z in omul(omul(omul(n,m),bar(n)),bar(m)))
  for x in V:assert act(i,act(j,x))==mul(mul(red(c),act(j,act(i,x))),red(bar(c)))
 classes={min(x,mod(-z for z in x)) for x in f['units']}
 assert len({min(act(i,x),mod(-z for z in act(i,x))) for x in classes})==36
for r in range(3):
 for j in range(3):
  x=(r,0,j,0);z=mul(mul(x,x),x);assert (z[0],z[2])==(r,(-j)%3)
print('PASS: all4 original normalizer reduction squares, all81-element inverse actions/all ring products, actualF9 Frobenius at3, full36 projective-unit permutations, and all square/commutator inner corrections. No commuting W or canonical576 action inferred.')
