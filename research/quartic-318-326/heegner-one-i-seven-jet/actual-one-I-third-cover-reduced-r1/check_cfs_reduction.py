#!/usr/bin/env python3
"""Verify exact Cremona-Fisher-Stoll covariant reduction of the frozen xi cover."""
from pathlib import Path
import json,sys
import sympy as s
H=Path(__file__).resolve().parent
owner=Path(sys.argv[1]) if len(sys.argv)>1 else H.parent/'actual-one-I-third-cover-minimization-r1'/'EXACT-THIRD-COVER-MINIMIZATION.json'
prior=json.loads(owner.read_text())
data=json.loads((H/'EXACT-CFS-REDUCTION.json').read_text())
a,z=s.symbols('a z')
ij=tuple((i,j) for i in range(4) for j in range(i,4))
def hessian(row):
    T=s.zeros(4)
    for v,(i,j) in zip(row,ij):T[i,j]=T[j,i]=(2 if i==j else 1)*v
    return T
A,B=map(hessian,prior['transformed_coefficients'])
assert [A.tolist(),B.tolist()]==data['initial_H']
beta,p,q=(204618888056724185,data['p'],data['q'])
d=prior['d']
assert p==114649 and q==119851 and d==beta*p*q==data['d']
pencil=s.Poly((a*A+B).det(),a)
assert pencil==s.Poly(beta*(p*a*a-q)*(9*p*a*a-q),a)
assert pencil.all_coeffs()==data['pencil']
a4,_,a2,_,a0=pencil.all_coeffs()
T=(a*A.adjugate()+B.adjugate()).adjugate().applyfunc(s.expand)
M1=T.applyfunc(lambda c:c.coeff(a,2)/a4)
M2=T.applyfunc(lambda c:c.coeff(a,1)/a0)
assert T==a4*a4*A*a**3+(a4*M1)*a*a+(a0*M2)*a+a0*a0*B
roots=[s.sqrt(p*q)/(k*p)*sg for k in (1,3) for sg in (1,-1)]
def square_matrix(t):
    N=(a0/t*A+M1+t*M2+a4*t*t*B).applyfunc(s.simplify)
    assert N.rank()==1
    i=next(i for i in range(4) if N[i,i])
    return N*s.sign(N[i,i])
N=[square_matrix(t) for t in roots]
G0=(N[0]+N[1]).applyfunc(s.simplify)
G1=(N[2]+N[3]).applyfunc(s.simplify)
assert all(x.is_Rational for x in [*G0,*G1])
fp=pencil.diff()
assert s.simplify(fp.eval(roots[0])/fp.eval(roots[2]))==-3
Gram=G0+s.sqrt(3)*G1
U,V=map(s.Matrix,(data['U'],data['V']))
assert U.shape==(4,4) and V.shape==(2,2) and abs(U.det())==abs(V.det())==1
Y=U.T*Gram*U
# Verify exact LLL Gram inequalities algebraically, not a floating Cholesky.
K=s.QQ.algebraic_field(s.sqrt(3))
def sgn(x):
    a,b=(x.to_list()+[0,0])[:2] if len(x.to_list())==2 else (0,x.to_list()[0] if x.to_list() else 0)
    if a==0:return int(b>0)-int(b<0)
    if b==0:return int(a>0)-int(a<0)
    if (a>0)==(b>0):return int(a>0)-int(a<0)
    ss=3*a*a-b*b
    return (int(a>0)-int(a<0))*(int(ss>0)-int(ss<0))
G=Y.applyfunc(s.expand)
c=[[K.from_sympy(G[i,j]) for j in range(4)] for i in range(4)]
r=[];mu=[[K.zero]*4 for _ in range(4)]
for i in range(4):
    r.append(c[i][i]-sum((mu[i][j]**2*r[j] for j in range(i)),K.zero))
    assert sgn(r[-1])==1
    for j in range(i+1,4):
        mu[j][i]=(c[j][i]-sum((mu[j][k]*mu[i][k]*r[k] for k in range(i)),K.zero))/r[i]
        assert sgn(K.convert(1)/2-mu[j][i])>=0 and sgn(K.convert(1)/2+mu[j][i])>=0
    if i:assert sgn(r[i]-(K.convert(3)/4-mu[i][i-1]**2)*r[i-1])>=0
HH=[U.T*T*U for T in [A,B]]
Q=s.Matrix([[X[i,j]/(2 if i==j else 1) for i,j in ij] for X in HH])
assert (V*Q).tolist()==data['reduced']
old=max(abs(v) for Q in prior['transformed_coefficients'] for v in Q)
new=max(abs(v) for v in V*Q)
assert old==145243861686420236632126 and new==181008208
assert new*10**14<old
# Exact homogeneous shape of the marked target:
# Umark=3p*a, Vmark=z gives beta*(3p*Y/beta)^2=(Umark²-P Vmark²)(Umark²-9P Vmark²).
P=p*q
rhs=((3*p*a)**2-P*z*z)*((3*p*a)**2-9*P*z*z)
assert s.expand(rhs-(9*p*p//1)* (beta*(p*a*a-q*z*z)*(9*p*a*a-q*z*z))/beta)==0
print(json.dumps(dict(old_max=int(old),new_max=int(new),det_U=int(U.det()),det_V=int(V.det()),
                      d=d,mark_A='3p*a/z',mark_V='3p*Y/(beta*z^2)',
                      lll_delta='3/4',exact_eigen_radicand=3,checked=True),sort_keys=True,indent=2))
