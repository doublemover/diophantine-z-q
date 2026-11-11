import sympy as s,json,hashlib
from pathlib import Path
D=Path(__file__).parent
A,B=s.symbols('A B',nonzero=True)
def reduce(x):return s.Poly(s.expand(s.cancel(x)),A,B).rem(s.Poly(A*A-210,A,B)).as_expr() if False else s.rem(s.rem(s.together(x).as_numer_denom()[0],A*A-210,A),B*B-5,B).expand()
def split(p):
 a,b,c,d=p
 return s.Matrix([[a+(1+B)*b/2,A*((B-5)*c-2*B*d)/10],[A*((B+5)*c-2*B*d)/10,a+(1-B)*b/2]])
def unsplit(M):return s.Matrix([((B-1)*M[0,0]+(B+1)*M[1,1])/(2*B),(M[0,0]-M[1,1])/B,(M[1,0]-M[0,1])/A,((B-5)*M[1,0]-(B+5)*M[0,1])/(2*A*B)])
def prod(x,y):return s.Matrix([x[0]*y[0]-210*x[1]*y[1]-84*x[1]*y[3]+x[2]*y[2]-126*x[3]*y[1]-42*x[3]*y[3],x[0]*y[1]+x[1]*y[0]-2*x[1]*y[2]+3*x[2]*y[1]+x[2]*y[3]-x[3]*y[2],x[0]*y[2]+x[2]*y[0]-42*x[1]*y[3]+x[2]*y[2]+42*x[3]*y[1],x[0]*y[3]+x[3]*y[0]+5*x[1]*y[2]-5*x[2]*y[1]-2*x[2]*y[3]+3*x[3]*y[2]])
def frm(p):return s.Matrix([p[0],p[3],p[1],p[2]-2*p[3]])
def to(x):return s.Matrix([x[0],x[2],x[3]+2*x[1],x[1]])
p=s.Matrix(s.symbols('p0:4'));q=s.Matrix(s.symbols('q0:4'))
assert all(s.simplify(x)==0 for x in unsplit(split(p))-p)
M=s.Matrix(2,2,s.symbols('m0:4'))
assert all(s.simplify(x)==0 for x in split(unsplit(M))-M)
E=lambda M,N:-((M[0,0]*N[0,1]-M[0,1]*N[0,0])+(M[1,0]*N[1,1]-M[1,1]*N[1,0]))/A
J=s.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
assert reduce(E(split(p),split(q))-(p.T*J*q)[0])==0
basis=[s.eye(4)[:,i] for i in range(4)]
for x in basis:
 for y in basis:assert all(reduce(v)==0 for v in split(to(prod(x,y)))-split(to(x))*split(to(y)))
u=s.Matrix([1,0,1,0]);ui=s.Matrix([2,0,-1,0]);one=s.Matrix([1,0,0,0])
assert prod(u,ui)==one and prod(ui,u)==one
T=lambda u:s.Matrix.hstack(*(to(prod(frm(p),u)) for p in basis))
assert T(u)*T(ui)==s.eye(4) and T(u).T*J*T(u)==J
assert T(-one)==-s.eye(4)
r={'kind':'independent symbolic regression, not Lean kernel validation','checks':['exact split and inverse on all symbolic vectors/matrices','full original symplectic pairing modulo alpha^2=210,beta^2=5','all16 literal integral-order basis products','actual nontrivial norm-one unit1+e2 and inverse2-e2','full integral symplectic matrix and true central-minus action'],'result':'PASS','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(D/'SYMBOLIC-REGRESSION.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS',r['checks'])
