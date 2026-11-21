#!/usr/bin/env python3
"""Exact arithmetic controls for the signed matrix/dt inverse; not a PEL model."""
from fractions import Fraction as Q
import json
from math import prod

class G:
    def __init__(self, a=0, b=0):
        self.a, self.b = Q(a), Q(b)
    def __add__(self, y):
        y = g(y)
        return G(self.a+y.a, self.b+y.b)
    __radd__ = __add__
    def __neg__(self):
        return G(-self.a, -self.b)
    def __sub__(self, y):
        return self + -g(y)
    def __mul__(self, y):
        y = g(y)
        return G(self.a*y.a-self.b*y.b, self.a*y.b+self.b*y.a)
    __rmul__ = __mul__
    def __truediv__(self, y):
        y = g(y)
        q = self * G(y.a,-y.b)
        return G(q.a/y.n(),q.b/y.n())
    def __eq__(self, y):
        y = g(y)
        return self.a==y.a and self.b==y.b
    def n(self):
        return self.a*self.a+self.b*self.b

def g(a):
    return a if isinstance(a,G) else G(a)

def mm(A,B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))

def tm(A):
    return tuple(zip(*A))

def sm(c,A):
    return tuple(tuple(g(c)*a for a in r) for r in A)

def det(A):
    return A[0][0]*A[1][1]-A[0][1]*A[1][0]

def f(mat,i,j):
    return mat[i][j]

I=((G(1),G(0)),(G(0),G(1)))
J=((G(0),G(-1)),(G(1),G(0)))
minusJ=sm(-1,J)
cs=(-14,-6,42,-21)
contacts=(0,32,76832,-343)
J0=2765952000
matrices=section_checks=0
signed_sample=None
for a in range(-4,5):
    for b in (2,3,5,7):
        mu=((G(a),G(b)),(G(-Q(210+a*a,b)),G(-a)))
        assert det(mu)==210
        assert mm(mu,mu)==sm(-210,I)
        nu=sm(-Q(1,210),mu)
        for h in range(1,9):
            X=((G(a+h,2),G(1-h,b)),(G(-2,a),G(b,h)))
            c=det(X)
            assert c!=0
            u=G(Q(h+1,b),Q(a+6,h))
            assert u!=0
            # Formal exact-identity canary: replace pi by a nonzero
            # rational parameter consistently, never as a metric estimate.
            pi=Q(h+5,b+2)
            turn=G(0,2*pi)
            M=sm(G(1)/turn,mm(mu,minusJ))
            Lam=sm(turn,mm(J,nu))
            assert mm(Lam,M)==I
            assert det(M)==G(210)/(turn*turn)
            # Evaluate each original bilinear pairing directly on the
            # columns of X, rather than using the determinant prediction.
            B=tuple(tuple(u*sum(f(X,k,i)*f(M,k,l)*f(X,l,j)
                        for l in range(2) for k in range(2))
                        for j in range(2)) for i in range(2))
            assert B==sm(u,mm(mm(tm(X),M),X))
            Delta=det(B)
            assert Delta==c*c*(G(210)/(turn*turn))*u*u
            matrices+=1
            for t in (Q(3,7),Q(-32,41),Q(34,11),Q(320,9)):
                Pt=prod(t-b0 for b0 in contacts)
                for v,b0 in zip(cs,contacts):
                    rho=Q(v)/(4*(t-b0))
                    kap=g(rho)/Delta
                    assert kap*Delta==rho
                    assert kap*c*c*(G(210)/(turn*turn))*u*u==rho
                    # The same 210*inverse of both actual scaled
                    # section coefficients, before any metric.
                    for coord in (Q(J0*J0)/Pt, t*Q(J0*J0)/Pt):
                        branch=coord/rho
                        invA=g(210*branch)*kap
                        invB=g(210*coord)/Delta
                        assert invA==invB and invA*Delta==210*coord
                        section_checks+=1
                    y=Q(h+2,b+1)
                    Falt2=c.n()*210*y*y/(pi*pi)
                    Petersson=Q(4)*abs(rho)*y*y/u.n()
                    # Check |kap|·Falt2 = Petersson by squaring.
                    assert kap.n()*Falt2*Falt2==Petersson*Petersson
                    if signed_sample is None:
                        signed_sample = dict(q=str(t),rho=str(rho),
                             Delta=[str(Delta.a),str(Delta.b)],
                             kappa=[str(kap.a),str(kap.b)])
print(json.dumps(dict(matrix_controls=matrices,
                    signed_branch_controls=section_checks//2,
                    literal_integral_inverse_controls=section_checks,
                    contacts=contacts,twists=cs,signed_sample=signed_sample,
                    scope="exact Gaussian-rational identities; no geometric or analytic L-value computation"),sort_keys=True,indent=2))
