from pathlib import Path
import sympy as s,re,ast,itertools
p=Path('quartics/quartic-318-326/proof/experiments/pel-normalizer-norm-support-r1/PELNormalizerQuadraticCertificates318.lean')
t=p.read_text();body=t.split('@[expose] def coefficient')[1].split('/--')[0].split(':=',1)[1];C=ast.literal_eval(body.replace('!','').strip());assert len(C)==10 and all(len(x)==16 for x in C)
a=s.symbols('a0:4')
def embed(x):return s.Matrix([x[0]+x[2]/2,x[1]+x[3]/2,x[2]/2,x[3]/10])
def coords(x):return s.Matrix([x[0]-x[2],x[1]-5*x[3],2*x[2],10*x[3]])
def mul(x,y):
 r,i,j,k=x;R,I,J,K=y
 return s.Matrix([r*R-210*i*I+5*j*J+1050*k*K,r*I+i*R-5*j*K+5*k*J,r*J+j*R-210*i*K+210*k*I,r*K+k*R+i*J-j*I])
x=embed(a);bar=s.Matrix([x[0],-x[1],-x[2],-x[3]])
N=[]
for j in range(4):N.extend(coords(mul(mul(x,embed(s.eye(4)[:,j])),bar)))
for row,(i,j) in zip(C,[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]):assert s.expand(sum(c*n for c,n in zip(row,N))-210*a[i]*a[j])==0,(i,j)
primes=[2,3,5,7];vals={s.prod(p**b for p,b in zip(primes,v)) for v in itertools.product([0,1],repeat=4)};assert vals=={n for n in range(1,211) if 210%n==0}
for v in itertools.product([0,1],repeat=4):
 for w in itertools.product([0,1],repeat=4):
  norm=lambda b:s.prod(p**i for p,i in zip(primes,b))
  assert norm(v)*norm(w)==norm([(i+j)%2 for i,j in zip(v,w)])*norm([i*j for i,j in zip(v,w)])**2
print('PASS: all10 exact210 quadratic certificates from independent quaternion multiplication; all16 positive divisors; all256 original word norm cocycles.')
