#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import re,ast,sympy as s
P=Path(__file__).resolve().parent.parent
v=lambda t:[ast.literal_eval('['+r+']') for r in re.findall(r'!\[([^\[\]]+)\]',t)]
t=(P/'PELOriginalRamifiedResidues318.lean').read_text();aa=v(t.split('def quadraticA',1)[1].split('\n',1)[0])[0];bb=v(t.split('def quadraticB',1)[1].split('\n',1)[0])[0]
primes=[2,3,5,7]
nt=(P/'PELPrimeNormalizerData318.lean').read_text();ns=v(nt.split('def coefficients',1)[1].split('\n\n',1)[0])
ct=(P/'PELPrimeRightLattice318.lean').read_text();bars=v(ct.split('def conjugateCoefficients',1)[1].split('\n\n',1)[0])
def mul(x,y):
 a,b,c,d=x;A,B,C,D=y
 return(a*A-210*b*B-84*b*D+c*C-126*d*B-42*d*D,a*B+b*A-2*b*C+3*c*B+c*D-d*C,a*C+c*A-42*b*D+c*C+42*d*B,a*D+d*A+5*b*C-5*c*B-2*c*D+3*d*C)
def norm(x):a,b,c,d=x;return a*a+a*c+210*b*b+210*b*d-c*c+42*d*d
def residue(i,x):return (x[0]+3*x[2],x[3]) if i==2 else (x[0],x[2])
def qm(i,x,y):r,t=x;R,T=y;return(r*R+aa[i]*t*T,r*T+t*R+bb[i]*t*T)
def qn(i,x):r,t=x;return r*r+bb[i]*r*t-aa[i]*t*t
x=s.symbols('x0:4');y=s.symbols('y0:4')
for i,p in enumerate(primes):
 assert all((r*r-aa[i]-bb[i]*r)%p for r in range(p))
 L=residue(i,mul(x,y));R=qm(i,residue(i,x),residue(i,y))
 for a,b in zip(L,R):assert s.Poly(a-b,*x,*y,modulus=p).is_zero
 assert s.Poly(qn(i,residue(i,x))-norm(x),*x,modulus=p).is_zero
 assert mul(ns[i],bars[i])==(p,0,0,0)==mul(bars[i],ns[i])
 assert all(c%p==0 for c in residue(i,ns[i])+residue(i,bars[i]))
 coords=list(product(range(p),repeat=4));ker={a for a in coords if all(z%p==0 for z in residue(i,a))}
 image={tuple(z%p for z in mul(a,ns[i])) for a in coords}
 assert ker==image and len(ker)==p*p
 assert len({tuple(z%p for z in residue(i,a)) for a in coords})==p*p
 assert all(all(z%p==0 for z in mul(a,b)) for a,b in product(ker,repeat=2))
 for a in product(range(-2,3),repeat=4):
  b=a;power=(1,0,0,0)
  for k in range(1,5):
   c=mul(b,bars[i]);ok=all(z%p==0 for z in c)
   assert ok==(norm(b)%p==0)
   if not ok:break
   b=tuple(z//p for z in c)
   power=mul(power,ns[i])
   assert mul(b,power)==a
   assert norm(a)==p**k*norm(b)
print('PASS: original4 ring maps and irreducible residue polynomials, literal kernels=O*n_p, residue fields4/9/25/49, all kernel products modp, original n*bar(n)=p, norm compatibility and signed repeated actual division. Not a completion or conjugacy/orbit theorem.')
