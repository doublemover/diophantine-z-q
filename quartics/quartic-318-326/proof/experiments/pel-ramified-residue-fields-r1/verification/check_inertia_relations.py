#!/usr/bin/env python3
from pathlib import Path
import runpy
P=Path(__file__).resolve().parents[1]
a=runpy.run_path(str(P/'verification/check_inertia_normalizers.py'))
mul,norm,bar,s=a['mul'],a['norm'],a['bar'],a['s']
vec=a['vec'];N=[(-6,-2,-4,3),(-6,-2,-3,3),(-2,0,-1,0),(-7,-5,-7,7)]
U=[(191,-73,-39,105),(-547,-91,447,110),(-169,34,69,-51),(-89,20,31,-30),(1429,76,-987,-66)]
V=[(152,73,39,-105),(-100,91,-447,-110),(-100,-34,-69,51),(-58,-20,-31,30),(442,-76,987,66)]
L=[[0,1,2],[0,1,3],[0,2,3],[1,2,3],[0,1,2,3]]
t=(P/'PELInertiaPrimeWord318.lean').read_text()
for u,v in zip(U,V):assert vec(u) in t and vec(v) in t
one=s.Matrix([1,0,0,0])
for e,l,u,v,d in zip(a['A'],L,U,V,a['D']):
 word=one
 for j in l:word=mul(word,N[j])
 assert norm(word)==d
 assert mul(u,v)==one and mul(v,u)==one and norm(u)==1
 assert mul(u,word)==s.Matrix(e)
prod=one
for e in a['A']:prod=mul(prod,e)
r=s.Matrix([13,-2,13,4]);ri=s.Matrix([26,2,-13,-4])
t=(P/'PELInertiaFivefoldRelation318.lean').read_text();assert vec(r) in t and vec(ri) in t
assert prod==44100*r and 44100==210**2 and norm(r)==1 and mul(r,ri)==one and mul(ri,r)==one
print('PASS: all five exact original-label prime words, actual connecting norm-one units/inverses, and complete fivefold relation44100*residualUnit. No quotient cardinality or moduli identification inferred.')
