#!/usr/bin/env python3
"""Exact symbolic checks only. This does not compile Lean or prove maximality."""
import sympy as s

def mul(x,y):
    r,i,j,k=x; a,b,c,d=y
    return s.Matrix([r*a-210*i*b+5*j*c+1050*k*d,
        r*b+i*a-5*j*d+5*k*c,
        r*c+j*a-210*i*d+210*k*b,
        r*d+k*a+i*c-j*b])

def star(x): return s.Matrix([x[0],-x[1],-x[2],-x[3]])
def rosati(x): return s.Matrix([x[0],-x[1],x[2],x[3]])
def trace(x): return 2*x[0]
def E(x,y): return 2*(x[1]*y[0]-x[0]*y[1]+5*x[2]*y[3]-5*x[3]*y[2])
T=s.Matrix([[1,0,s.Rational(1,2),0],[0,1,0,s.Rational(1,2)],
            [0,0,s.Rational(1,2),0],[0,0,0,s.Rational(1,10)]])
assert T.det()==s.Rational(1,20)
for i in range(4):
    assert all(v.q==1 for v in T.inv()*rosati(T[:,i]))
    for j in range(4):
        assert all(v.q==1 for v in T.inv()*mul(T[:,i],T[:,j]))
G=s.Matrix(4,4,lambda i,j:E(T[:,i],T[:,j]))
assert G==s.Matrix([[0,-2,0,-1],[2,0,1,0],[0,-1,0,0],[1,0,0,0]])
assert G.det()==1
H=s.Matrix(4,4,lambda i,j:trace(mul(T[:,i],T[:,j])))
assert H.det()==-44100
x=s.Matrix(s.symbols('x0:4')); y=s.Matrix(s.symbols('y0:4')); a=s.Matrix(s.symbols('a0:4'))
assert s.expand(E(mul(a,x),y)-E(x,mul(rosati(a),y)))==0
f=s.Matrix(s.symbols('f0:4'))
v=s.Matrix([-f[3],f[2],2*f[3]-f[1],f[0]-2*f[2]])
assert v.T*G==f.T
print('PASS: all 16 order products, Rosati, index 20, exact perfect Gram, trace determinant -44100, adjoint and unique-dual formula')
