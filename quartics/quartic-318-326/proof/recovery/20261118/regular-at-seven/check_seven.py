#!/usr/bin/env python3
from pathlib import Path
import itertools,re
f=Path(__file__).with_name('inputs')/'OriginalIntegerAffineModel318.lean'
cx=list(map(int,re.search(r'def contacts : Fin 4 → ℤ := !\[([^\]]+)\]',f.read_text())[1].split(',')))
assert cx==[0,32,32*7**4,-7**3] and [z%7 for z in cx]==[0,4,0,0]
assert (-32)%7==3 and all(i*i%7!=3 for i in range(7))
# Projectivize over F49 to exercise all three dehomogenizations
F=list(itertools.product(range(7),repeat=2)); zero=(0,0); one=(1,0)
def add(x,y):return tuple((a+b)%7 for a,b in zip(x,y))
def mul(x,y):return ((x[0]*y[0]+3*x[1]*y[1])%7,(x[0]*y[1]+x[1]*y[0])%7)
def sm(k,x):return tuple(k*a%7 for a in x)
n=0
for I in range(3):
 for t in itertools.product(F,repeat=2-I):
  w,a,c=(*([zero]*I),one,*t)
  if add(add(mul(c,c),sm(-1,mul(a,a))),sm(32,mul(w,w)))!=zero:continue
  grad=(sm(64,w),sm(-2,a),sm(2,c))
  assert any(g!=zero for i,g in enumerate(grad) if i!=I)
  n+=1
assert n==50
print('PASS: contact valuations, F49 centre, 50 projective F49 conic directions; local gradient nonzero. Not a regularity proof.')
