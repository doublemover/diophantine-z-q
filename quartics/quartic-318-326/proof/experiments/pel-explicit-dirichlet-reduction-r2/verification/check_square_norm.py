#!/usr/bin/env python3
from pathlib import Path
import sympy as s,re,ast
P=Path(__file__).resolve().parent.parent
t=(P/'PELIntegralUnitSpan318.lean').read_text()
def rows(name):
 z=t.split('def '+name,1)[1].split('\n\n',1)[0]
 return [list(ast.literal_eval('['+v+']')) for v in re.findall(r'!\[([^\[\]]+)\]',z)]
U=s.Matrix.hstack(*(s.Matrix(v) for v in rows('coefficients')));A=s.Matrix(rows('expansion'))
assert U.shape==(4,5) and A.shape==(4,5)
assert U*A.T==s.eye(4)
def embed(a):return (a[0]+s.Rational(1,2)*a[2],a[1]+s.Rational(1,2)*a[3],s.Rational(1,2)*a[2],s.Rational(1,10)*a[3])
def mul(x,y):
 r,i,j,k=x;R,I,J,K=y
 return(r*R-210*i*I+5*j*J+1050*k*K,r*I+i*R-5*j*K+5*k*J,r*J+j*R-210*i*K+210*k*I,r*K+k*R+i*J-j*I)
def norm(x):r,i,j,k=x;return r*r+210*i*i-5*j*j-1050*k*k
assert [norm(embed(list(U[:,j]))) for j in range(5)]==[1,-1,1,1,1]
x=s.symbols('r i j k');y=s.symbols('R I J K');B=[embed(list(s.eye(4)[:,j])) for j in range(4)]
def co(x):r,i,j,k=x;return(r-j,i-5*k,2*j,10*k)
assert s.expand(sum(co(mul(mul(x,B[j]),y))[j] for j in range(4))-4*x[0]*y[0])==0
for j in range(4):
 lhs=2*mul(x,B[j])[0]
 rhs=sum(A[j,z]*2*mul(x,embed(list(U[:,z])))[0] for z in range(5))
 assert s.expand(lhs-rhs)==0
print('PASS: exact five original unit columns/norm signs; integer reconstruction of ALL original basis vectors; full sandwich trace polynomial and all4 trace expansions. Not hosted Lean or parity-support acceptance.')
