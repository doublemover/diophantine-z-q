"""Independent exact rational checks; not Lean/kernel acceptance."""
import sympy as s
P=s.Matrix([[1,0,s.Rational(1,2),0],[0,1,0,s.Rational(1,2)],[0,0,s.Rational(1,2),0],[0,0,0,s.Rational(1,10)]])
def mul(x,y):
 r,i,j,k=x;R,I,J,K=y
 return s.Matrix((r*R-210*i*I+5*j*J+1050*k*K,r*I+i*R-5*j*K+5*k*J,r*J+j*R-210*i*K+210*k*I,r*K+k*R+i*J-j*I))
def pairing(x,y):
 r,i,j,k=x;R,I,J,K=y
 return 2*(i*R-r*I+5*j*K-5*k*J)
def rosati(x):return s.Matrix((x[0],-x[1],x[2],x[3]))
x=s.symbols('x:4');y=s.symbols('y:4');a=s.symbols('a:4')
assert s.expand(pairing(mul(a,x),y)-pairing(x,mul(rosati(a),y)))==0
b=[P[:,i] for i in range(4)]
assert all(z.q==1 for u in b for v in b for z in P.inv()*mul(u,v))
assert all(z.q==1 for u in b for z in P.inv()*rosati(u))
G=s.Matrix(4,4,lambda i,j:pairing(b[i],b[j]))
assert G==s.Matrix([[0,-2,0,-1],[2,0,1,0],[0,-1,0,0],[1,0,0,0]])
assert G.det()==1 and P.det()==s.Rational(1,20)
T=s.Matrix(4,4,lambda i,j:2*mul(b[i],b[j])[0]);assert T.det()==-44100
v=s.Matrix((-y[3],y[2],2*y[3]-y[1],y[0]-2*y[2]));assert v.T*G==s.Matrix([list(y)])
print('PASS: exact quaternion adjoint, all16 order products, Rosati stability, index20, integral Gram determinant1, trace discriminant210 and explicit dual vector. Not maximality/ramification or Lean acceptance.')
