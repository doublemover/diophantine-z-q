#!/usr/bin/env python3
"""Actual maximal orders at all five F53 supersingular curves, with marked λ."""
import json
from fractions import Fraction as Qr
from pathlib import Path
import sys
from sympy import Integer, Matrix
from sympy.matrices.normalforms import hermite_normal_form
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from fixed48_hecke_mod13_r2 import *

q=13
m=q*q


def addk(x,y):
    return (x[0]+y[0],x[1]+y[1])


def negk(x):
    return (-x[0],-x[1])


def sc(c,x):
    return (c*x[0],c*x[1])


def mulk(x,y):
    a,b=x
    c,d=y
    return (a*c-b*d,a*d+b*c-b*d)


def conjk(x):
    return (x[0]-x[1],-x[1])


def coordinates(v):
    a,b,c,d=v
    Z=mulk((Qr(1,3),Qr(2,3)),(c,d))
    return addk((a,b),Z),Z


def reverse(x):
    A,B=x
    return (*addk(A,negk(B)),*mulk(B,(-1,-2)))


def multiply(x,y):
    A,B=coordinates(x)
    C,D=coordinates(y)
    return reverse((addk(mulk(A,C),sc(-p,mulk(B,conjk(D)))),
                    addk(mulk(A,D),mulk(B,conjk(C)))))


def trace(x):
    A,B=coordinates(x)
    return 2*A[0]-A[1]


def check_order(M,den):
    B=M/den
    L=B.inv()
    as_integers=lambda x: all(a.q==1 for a in L*Matrix(x))
    assert as_integers([1,0,0,0])
    bi=[tuple(Qr(str(v)) for v in B.col(i)) for i in range(4)]
    pairing=Matrix([[trace(multiply(x,y)) for y in bi] for x in bi])
    assert abs(pairing.det())==p*p
    for x in bi:
        for y in bi:
            z=multiply(x,y)
            assert as_integers(z) and trace(z).denominator==1


def modulo(M,r):
    return M.applyfunc(lambda x:int(x)%r)


def inverse_mod(M,r):
    return modulo(pow(int(M.det()),-1,r)*M.adjugate(),r)


def matrices_q2():
    r=next(x for x in range(3,m,q) if (x*x+x+1)%m==0)
    assert r==146
    omega=Matrix.diag(r,-1-r)
    F=Matrix([[0,-p],[1,0]])
    I=Matrix.eye(2)
    gamma=(F-I)*inverse_mod(I+2*omega,m)
    mats=[modulo(M,m) for M in [I,omega,gamma,omega*gamma]]
    assert modulo(omega**2+omega+I,m)==Matrix.zeros(2)
    assert modulo(gamma*(I+2*omega)-(F-I),m)==Matrix.zeros(2)
    return r,mats


def other_order(v,matrices):
    a,b=v
    T=Matrix.hstack(Matrix(v),Matrix([0,1] if a else [1,0]))
    Ti=inverse_mod(T,m)
    As=[modulo(Ti*M*T,m) for M in matrices]
    flatten=lambda U:Matrix([U[0,0],U[1,0],U[0,1],U[1,1]])
    M=Matrix.hstack(*(flatten(A) for A in As))
    C=modulo(inverse_mod(M,m)*Matrix.diag(q,q*q,1,q),m)
    L=hermite_normal_form(Matrix.hstack(C,m*Matrix.eye(4)))
    assert L.det()==q**4
    for j in range(4):
        A=modulo(sum((int(L[i,j])*As[i] for i in range(4)),Matrix.zeros(2)),m)
        assert A[0,0]%q==A[1,1]%q==0 and A[1,0]==0
    check_order(L,q)
    return L


def coord(P):
    return None if P is None else [list(x.v) for x in P]


def modset(A,P,Q,n):
    R=[A.mul(i,P) for i in range(n)]
    S=[A.mul(i,Q) for i in range(n)]
    IJ={(1,i):A.add(P,S[i]) for i in range(n)}
    ell=2 if n%2==0 else 3
    IJ.update({(ell*i,1):A.add(R[ell*i],Q) for i in range(n//ell)})
    D={A.add(u,v):(i,j) for i,u in enumerate(R) for j,v in enumerate(S)}
    assert len(D)==n*n and len(set(IJ.values()))==n+n//ell
    return D,IJ


def curve_j(B):
    return tuple((1728*4*B.A**3/(4*B.A**3+27*B.B**2)).subfield())


def eval_level_bases(A,omega,F,J):
    mod16_P=D8.generator(16,2)
    mod16_Q=omega(mod16_P)
    mod3_P,mod3_Q=basis(D8,A0,p**4-1,3,3,8,3)
    U,V=basis(D8,A0,p**4-1,9,3,8,9)
    d9,_=modset(A,U,V,9)
    jlifts={J(X):X for X in d9 if A.mul(3,J(X)) is None}
    assert len(jlifts)==9
    gammas={3:lambda x: A.add(F(jlifts[x]),A.mul(-1,jlifts[x])),
            16:lambda x: A.add(F(A.mul(5,J(x))),A.mul(-5,J(x)))}
    # [5]J is the inverse of J modulo16 since 5*(-3)=1 modulo16.
    Bs={16:(mod16_P,mod16_Q),3:(mod3_P,mod3_Q)}
    ret={}
    for n,(P,Q) in Bs.items():
        points,lines=modset(A,P,Q,n)
        g=gammas[n]
        assert all(g(J(x))==A.add(F(x),A.mul(-1,x)) for x in points)
        mats=[Matrix.hstack(*(Matrix(points[a(x)]) for x in [P,Q]))
              for a in [lambda x:x,omega,g,lambda x:omega(g(x))]]
        ret[n]=((P,Q),mats,lines)
    return ret


def main():
    install()
    A=E(D8,A0)
    assert A0==[[0,0],[1,0]]
    F=lambda P: None if P is None else tuple(x**p for x in P)
    # Same ζ and actual CM automorphism as the finite oriented source.
    zeta=D8.zeta
    omega=lambda P: None if P is None else (zeta*P[0],P[1])
    assert zeta*zeta+zeta+1==D8.zero
    J=lambda P: A.add(P,A.mul(2,omega(P)))
    for y in (1,-1):
        assert J((D8.zero,y*D8.one)) is None
    P,Q0=basis(D8,A0,p**4-1,q,q,8,q)
    P=next(T for H in [P,Q0] if (T:=A.add(omega(H),A.mul(-9,H))) is not None)
    Q=F(P)
    assert A.mul(q,P) is None and A.mul(q,Q) is None
    assert omega(P)==A.mul(3,P) and omega(Q)==A.mul(9,Q)
    assert Q not in [A.mul(i,P) for i in range(q)]
    assert F(Q)==A.mul(-p,P)
    r,mats=matrices_q2()
    check_order(Matrix.eye(4),1)
    candidates={}
    line_vectors=[(1,i) for i in range(q)]+[(0,1)]
    for v in line_vectors:
        G=A.add(A.mul(v[0],P),A.mul(v[1],Q))
        map0=faster_odd_edge(D8,A,G,q)
        j=curve_j(E(D8,map0.dst))
        if j!=(0,0) and j not in candidates:
            # Check whole actual kernel with same normalized map, and
            # independently compare its Võlu evaluation and codomain.
            B,V=A.quotient(G,q)
            evm=map0.at(D8)
            assert coeffs(B)==map0.dst
            assert all(evm(A.mul(i,G)) is None for i in range(q))
            bs=basis(D8,A0,p**4-1,16,2,8,27)
            assert all(evm(X)==V(X) for X in bs)
            candidates[j]=(v,G,map0)
    expected=[(0,0),(28,21),(28,32),(46,0),(50,0)]
    assert set(candidates)==set(expected[1:])
    mark=eval_level_bases(A,omega,F,J)
    source=SRC.read_bytes()
    assert hashlib.sha256(source).hexdigest().startswith("421d8068")
    table=json.loads(source)
    lookup={pointkey(r):r['rows'][0]['phi'] for r in table['records']}
    Aout=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    W=short((D8.F.of(22),15*D8.u))
    values={Aout.mul(j,W):j for j in range(q)}
    assert len(values)==q
    used=set()
    result=[]
    for k in expected:
        if k==(0,0):
            v=G=map0=None
            L=Matrix.eye(4)
            den=1
            B=A
            f=lambda x:x
        else:
            v,G,map0=candidates[k]
            L=other_order(v,mats)
            den=q
            B=E(D8,map0.dst)
            f=map0.at(D8)
        same={}
        for a,U in mark[16][2].items():
            for b,V in mark[3][2].items():
                address=tkey(B,f(U),f(V))
                ph=lookup[address]
                v13=values[Aout.mul(224,short(tuple(parse(D8,ph))))] if ph else 0
                same.setdefault(address,{'t16_and_after3':address,
                    'inverse_transport_mark':[a,b],'lambda13_phi0':v13})
        assert len(same)==(32 if den==1 else 96)
        assert not (used&same.keys())
        used.update(same)
        result.append(dict(j=k,max_order_basis_columns=L.tolist(),basis_denominator=den,
           target=coeffs(B),kernel_mod13=v,kernel_geometric_generator=coord(G),
           normalized_velu_map=None if not map0 else
             dict(num=map0.num,den=map0.den,differential=map0.der),
           exact_marks=[same[s] for s in sorted(same)]))
    assert len(used)==len(lookup)==416
    signed={tuple(row['t16_and_after3']):row['lambda13_phi0']
            for cls in result for row in cls['exact_marks']}
    conj=lambda x:(x[0],-x[1]%53,x[2],-x[3]%53)
    assert all(signed[conj(k)]==-z%q for k,z in signed.items())
    def json_int(x):
        assert isinstance(x,Integer),type(x)
        return int(x)
    print(json.dumps(dict(first_O_basis=['1','omega','gamma','omega gamma'],
        source_E0=A0,embedding='gamma=(Frobenius-1)/(right J), J=1+2*omega',
        q13_basis=[coord(P),coord(Q)],q2_omega_eigen_r=r,
        q2_matrices=[M.tolist() for M in mats],
        actual_level_bases={n:[coord(X) for X in mark[n][0]] for n in mark},
        exact_level_matrices={n:[M.tolist() for M in mark[n][1]] for n in mark},
        marked_classes=result),indent=2,sort_keys=True,default=json_int))


if __name__=='__main__':
    main()
