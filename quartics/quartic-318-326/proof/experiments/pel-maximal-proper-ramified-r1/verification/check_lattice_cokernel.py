#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import runpy
P=Path(__file__).resolve().parents[1]
a=runpy.run_path(str(P/'verification/check_parity.py'))
s,mul,norm,bar,N=a['s'],a['mul'],a['norm'],a['bar'],a['N']
rows=[(1,3),(1,3),(0,1),(1,3)]
L=[[[0,1],[0,0],[1,0],[0,0]],[[2,0],[0,0],[0,2],[0,0]],[[3,0],[0,0],[0,0],[0,4]],[[3,6],[0,0],[0,5],[0,0]]]
x=s.Matrix(s.symbols('x:4'));E=[s.eye(4)[:,i] for i in range(4)]
vec=lambda x:'!['+','.join(map(str,x))+']'
t=(P/'PELPrimeRightLattice318.lean').read_text()
assert vec([vec(bar(n)) for n in N]) in t
assert vec([vec(r) for r in rows]) in t
assert all(vec([vec(r) for r in l]) in (P/'PELPrimeLatticeResidues318.lean').read_text() for l in L)
for n,r,l in zip(N,rows,L):
 p=norm(n);n=s.Matrix(n);bn=bar(n);l=s.Matrix(l)
 right=s.Matrix.hstack(*[mul(e,n) for e in E]);back=s.Matrix.hstack(*[mul(e,bn) for e in E])
 assert right*back==p*s.eye(4) and back*right==p*s.eye(4)
 assert right.det()==p*p
 R=back.extract(r,range(4))
 assert all(v%p==0 for v in R*l-s.eye(2))
 assert all(v%p==0 for v in back-back*l*R)
 # This exact matrix identity reconstructs integral preimages when back*x is p-divisible.
 assert right*back*x==p*x
 image={tuple(int(v)%p for v in right*s.Matrix(a)) for a in product(range(p),repeat=4)}
 kernel={a for a in product(range(p),repeat=4) if all(v%p==0 for v in R*s.Matrix(a))}
 assert image==kernel and len(image)==p*p
 for z in product(range(p),repeat=2):assert tuple(int(v)%p for v in R*l*s.Matrix(z))==z
print('PASS: actual right-normalizer lattice maps, all four complete kernel reconstructions, every residue/output lift, both exact compositions[p], and indices4/9/25/49. No analytic/algebraic isogeny inferred.')
