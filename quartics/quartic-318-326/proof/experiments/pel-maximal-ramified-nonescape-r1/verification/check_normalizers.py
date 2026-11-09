from pathlib import Path
import sympy as s
P=Path(__file__).resolve().parent.parent
A=s.symbols('a:4');B=s.symbols('b:4');E=[tuple(int(i==j) for i in range(4)) for j in range(4)]
def mul(a,b):
 x,y,z,w=a;r,t,u,v=b
 return (x*r-210*y*t-84*y*v+z*u-126*w*t-42*w*v,x*t+y*r-2*y*u+3*z*t+z*v-w*u,x*u+z*r-42*y*v+z*u+42*w*t,x*v+w*r+5*y*u-5*z*t-2*z*v+3*w*u)
def norm(a):x,y,z,w=a;return x*x+x*z+210*y*y+210*y*w-z*z+42*w*w
def bar(a):x,y,z,w=a;return(x+z,-y,-z,-w)
def embed(a):x,y,z,w=a;return(x+s.Rational(1,2)*z,y+s.Rational(1,2)*w,s.Rational(1,2)*z,s.Rational(1,10)*w)
def qm(a,b):
 r,i,j,k=a;t,l,m,n=b
 return(r*t-210*i*l+5*j*m+1050*k*n,r*l+i*t-5*j*n+5*k*m,r*m-210*i*n+j*t+210*k*l,r*n+i*m-j*l+k*t)
def qb(a):r,i,j,k=a;return(r,-i,-j,-k)
def eq(a,b):assert all(s.expand(x-y)==0 for x,y in zip(a,b))
N=[(2,(-6,-2,-4,3)),(3,(-6,-2,-3,3)),(5,(-2,0,-1,0)),(7,(-7,-5,-7,7))]
vec=lambda a:'!['+','.join(map(str,a))+']'
source=(P/'PELPrimeNormalizerData318.lean').read_text();assert all(vec(a) in source for p,a in N)
conj=(P/'PELPrimeOrderConjugation318.lean').read_text()
relations=(P/'PELPrimeNormalizerRelations318.lean').read_text()
for p,a in N:
 assert norm(a)==p
 C=s.Matrix.hstack(*(s.Matrix(mul(mul(a,e),bar(a)))/p for e in E))
 D=s.Matrix.hstack(*(s.Matrix(mul(mul(bar(a),e),a))/p for e in E))
 assert all(v.q==1 for v in list(C)+list(D))
 assert C*D==D*C==s.eye(4)
 eq(C*s.Matrix(mul(A,B)),mul(C*s.Matrix(A),C*s.Matrix(B)))
 eq(embed(C*s.Matrix(A)),[x/p for x in qm(qm(embed(a),embed(A)),qb(embed(a)))])
 eq(embed(D*s.Matrix(A)),[x/p for x in qm(qm(qb(embed(a)),embed(A)),embed(a))])
 for M in [C,D]:
  for i in range(4):
   row='+'.join('('+str(M[i,j])+')*a '+str(j) for j in range(4) if M[i,j]) or '0'
   assert row in conj
 sq=tuple(x//p for x in mul(a,a));si=tuple(x//p for x in mul(bar(a),bar(a)))
 assert norm(sq)==norm(si)==1 and mul(sq,si)==mul(si,sq)==E[0]
 assert vec(sq) in relations and vec(si) in relations
 for q,b in N:
  comm=tuple(x//(p*q) for x in mul(mul(mul(a,b),bar(a)),bar(b)))
  assert norm(comm)==1 and mul(comm,bar(comm))==E[0]
  eq(mul(a,b),mul(comm,mul(b,a)));assert vec(comm) in relations
print('PASS: all4 original positive prime norms, literal8 integral conjugation matrices/inverses, full polynomial multiplication and quaternion identity,4 square norm-one units and all16 exact commutator units')
