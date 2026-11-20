#!/usr/bin/env python3
"""Actual one-unit row a=1: compose both vertical primes, not a fake pi."""
from pathlib import Path
import json
import sys
import hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'heegner-f53-oriented'))
import oriented_projection as D8
import first_descended_omega as D16
import field18 as D18
from random import Random

p=53
def read(M,x):
    a,b=x
    return a+b*M.u
def parse(M,S):
    return [read(M,x) for x in S]
def E(M,ab):
    return M.E(*parse(M,ab))
def coeffs(A):
    return [x.subfield() for x in [A.A,A.B]]
def peval(M,P,x):
    y=M.zero
    for a in reversed(P):y=y*x+a
    return y

class Morphism:
    """Exact k-rational x-map plus invariant differential behavior."""
    def __init__(self, src, dst, num, den, differential):
        self.src=src; self.dst=dst
        self.num=[x.subfield() for x in num]
        self.den=[x.subfield() for x in den]
        self.dn=[x.subfield() for x in D16.pder(num)]
        self.dd=[x.subfield() for x in D16.pder(den)]
        self.der=differential.subfield()
    def at(self,M):
        N,D,dN,dD=[parse(M,P) for P in [self.num,self.den,self.dn,self.dd]]
        w=read(M,self.der); T=E(M,self.dst)
        def f(P):
            if P is None:return P
            x,y=P
            n,d=peval(M,N,x),peval(M,D,x)
            if not d:return None
            Q=(n/d,y*(peval(M,dN,x)*d-n*peval(M,dD,x))/(d*d*w))
            assert T.contains(Q)
            return Q
        return f

def constant(M,x):return [x] if x else []
def times(c,P):return [c*x for x in P]
def odd_edge(M,A,G,l):
    """Vélu normalized map from the genuine odd kernel, compatible fields."""
    B,phi=A.quotient(G,l)
    target=coeffs(B); src=coeffs(A)
    K=[M.one]; s=M.zero
    for a in range(1,(l+1)//2):
        x,y=A.mul(a,G)
        K=[a+b for a,b in zip([(-x)*z for z in K]+[M.zero],[M.zero]+K)]
        s+=x
    K=parse(D16,[x.subfield() for x in K])
    a,b=parse(D16,src); z=D16.zero; o=D16.one
    f=[b,a,z,o]; fp=D16.pder(f)
    d=(l-1)//2
    der=D16.pder
    mul,add,neg=D16.pprod,D16.padd,D16.pneg
    D=mul(K,K)
    H=add(mul(der(K),der(K)),neg(mul(der(der(K)),K)))
    N=add(add(mul([-2*read(D16,s.subfield()),D16.F.of(2*d+1)],D),
              times(4,mul(f,H))),times(-2,mul(mul(fp,der(K)),K)))
    e=Morphism(src,target,N,D,o)
    mapped=e.at(M)
    for j in range(l):
        Q=A.mul(j,G)
        assert mapped(Q)==phi(Q)==None
    # At independent E(k)-sample inputs, confirm actual normalized Vélu.
    A16=E(D16,src)
    V=[(read(M,x.subfield()),read(M,y.subfield())) for x,y in D16.coordinates(A16,D16.one)[::139]]
    assert V and all(mapped(P)==phi(P) for P in V)
    return e

def arbitrary_basis(M,B,ell,r,seed,act):
    rng=Random(seed)
    k,m=(16,p**8-1) if M is D16 else (18,p**9+1)
    assert m%ell==0
    for _ in range(100):
        x=M.F.trim([rng.randrange(p) for _ in range(k)])
        y=M.sqrt(x**3+B.A*x+B.B)
        if y is None:continue
        S=B.mul(m//ell,(x,y))
        assert B.mul(ell,S) is None
        P=B.add(act(S),B.mul(r-1,S))
        if P is None:continue
        assert B.mul(ell,P) is None and act(P)==B.mul(r,P)
        return P
    raise AssertionError('no basis')

def mix(M,B,ell,act):
    A=E(M,B)
    r=D16.root%ell
    P=arbitrary_basis(M,A,ell,r,313,act.at(M))
    Q=arbitrary_basis(M,A,ell,1-r,997,act.at(M))
    assert Q not in [A.mul(i,P) for i in range(ell)]
    return P,Q

def map_point(M,F,P):
    for morph in F:P=morph.at(M)(P)
    return P

def point_dump(P):return [list(x.v) for x in P]

def phi48(A,g16,g3):
    E3,f=A.quotient(g3,3)
    a,b=D8.edges(A,g16,4),D8.edges(E3,f(g16),4)
    T,U=D8.haupt(a),D8.haupt(b)
    x,y=D8.chart(T,U)
    C=2*y-(x**4+1)
    r=(x-1/x)/2; s=C/(4*x*x)
    assert s*s==r**4+r*r+1
    if r:
        A0=(s+1)/(r*r); B0=(A0*A0-1)*r
        X,Y=2*A0+1,2*B0
    elif s==D8.one:
        return {'x48':x.subfield(),'y48':y.subfield(),
                't16':[T.subfield(),U.subfield()],'phi_based':[[3,0],[0,0]]}
    else:
        X,Y=D8.zero,D8.zero
    assert Y*Y==X*(X+1)*(X-3)
    target=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    Q=target.add((X-D8.F.of(2)/3,Y),(D8.F.of(3)-D8.F.of(2)/3,D8.zero))
    P=[(Q[0]+D8.F.of(2)/3).subfield(),Q[1].subfield()] if Q else None
    return {'x48':x.subfield(),'y48':y.subfield(),'t16':[T.subfield(),U.subfield()],
            'phi_based':P,'t2_untouched':[z.subfield() for z in a],
            't2_after3':[z.subfield() for z in b]}

def main():
    # E0 -> B by exact C17/C19, in this order.
    G17=D16.generator(17,17); M17=odd_edge(D16,D16.E0,G17,17)
    G19=D18.generator(19,19)
    M19=odd_edge(D18,E(D18,M17.dst),M17.at(D18)(G19),19)
    B=M19.dst; B16=E(D16,B)
    action,num,den=D16.descended_action(D16.E0,lambda P:map_point(D16,[M17,M19],P),B16)
    Omega=Morphism(B,B,num,den,(1+D16.u)/2)
    # Choose local roots using P/Q only once on this B. For this single row,
    # the common d-level root is the pairing of the full P,Q basis.
    P17,Q17=mix(D16,B,17,Omega); P19,Q19=mix(D18,B,19,Omega)
    T17=odd_edge(D16,B16,B16.add(P17,Q17),17)
    A19=E(D18,T17.dst); f=T17.at(D18)
    T19=odd_edge(D18,A19,A19.add(f(P19),f(Q19)),19)
    maps=[M17,M19,T17,T19]
    g16,g3=[map_point(D8,maps,D8.generator(n,l)) for n,l in [(16,2),(3,3)]]
    data=phi48(E(D8,T19.dst),g16,g3)
    data.update({
      'literal_twist_quotient_parameter':1,'quadratic_weight':1,
      'first_marked_cm_E17_and_B_coeffs':[M17.dst,M19.dst],
      'actual_mixed_after17_and_after19_coeffs':[T17.dst,T19.dst],
      'C19_on_original_source_generator':point_dump(G19),
      'B_P17':point_dump(P17),'B_Q17':point_dump(Q17),
      'B_P19':point_dump(P19),'B_Q19':point_dump(Q19),
      'B_Omega_xsha256':hashlib.sha256(json.dumps([Omega.num,Omega.den]).encode()).hexdigest(),
      'four_arrow_degrees':[17,19,17,19],
    })
    print(json.dumps(data,sort_keys=True,indent=2))

if __name__=='__main__': main()
