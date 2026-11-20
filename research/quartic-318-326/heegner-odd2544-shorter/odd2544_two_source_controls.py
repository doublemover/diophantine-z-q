#!/usr/bin/env python3
"""Two compatible smaller alternate fields against the frozen f48 even rows."""
import json
from itertools import product
from math import isqrt
import odd2544_reference_coefficients as src


def exact_reps_at(order,den,M):
    assert tuple(r[0] for r in order)==(den,0,0,0)
    V=src.reduce_basis([tuple(order[i][j] for i in range(1,4)) for j in range(1,4)])
    a,b,c=[src.disc_(v) for v in V]
    p,q,r=[int(2*src.inner(V[i],V[j])) for i,j in ((0,1),(0,2),(1,2))]
    g=4*a*b*c+p*q*r-a*r*r-b*q*q-c*p*p
    assert g>0
    z0=9*den*den*M
    X=isqrt((z0*(4*b*c-r*r))//g)
    Y=isqrt((z0*(4*a*c-q*q))//g)
    for x in range(-X,X+1):
        x0=a*x*x
        for y in range(-Y,Y+1):
            z1=q*x+r*y
            delta=z1*z1+4*c*(z0-x0-b*y*y-p*x*y)
            if delta<0:
                continue
            s=isqrt(delta)
            if s*s!=delta:
                continue
            for t in ((s,-s) if s else (0,)):
                z,rem=divmod(t-z1,2*c)
                if rem:
                    continue
                w=src.add(src.add(src.smul(x,V[0]),src.smul(y,V[1])),src.smul(z,V[2]))
                assert src.disc_(w)==z0
                yield w


def coefficient(book,D):
    # D is a fundamental signed discriminant of the fully fixed local type.
    neg=D<0
    l=146965 if neg else -323
    weights=src.FUND_WEIGHT_TYPEI_MINUS if neg else src.FUND_WEIGHT_TYPEI_PLUS
    M=-l*D
    assert M>0 and M%8==7 and M%3==2 and M%53!=0
    mm={int(v):src.matrix_mod_factory(A,int(v)) for v,A in book['exact_level_matrices'].items()}
    t0=next(x for x in range(1,53) if (-3*x*x+M)%53==0) if neg else None
    out=[]
    for cls in book['marked_classes']:
        den=cls['basis_denominator']
        rows={tuple(tuple(v) for v in row['inverse_transport_mark']):row['lambda13_phi0']
              for row in cls['exact_marks']}
        total=0
        for v in exact_reps_at(cls['max_order_basis_columns'],den,M):
            a=1 if den==1 else src.leg(l,29)
            for r in weights:
                a*=src.wtI(v,den,r)
                if not a:
                    break
            if not a:
                continue
            if neg:
                t=((3*v[0]+2*v[1]-v[2])*pow(3*den,-1,53))%53
                assert (t-t0)*(t+t0)%53==0
                if t!=t0:
                    a=-a
            vv16=mm[16](tuple(x%16 for x in v),den)
            vv3=mm[3](tuple(x%3 for x in v),den)
            mark16=src.marked_values(vv16,16,2)
            mark3=src.marked_values(vv3,3,3)
            for x,y in product(mark16,mark3):
                total+=a*rows.get((x,y),0)*src.leg(2*mark3[y]-vv3[0]-vv3[-1],3)
        out.append(total)
    total=sum(out)
    return dict(D=D,l=l,phase_coordinate=t0,raw_mod13_representatives_by_class=out,
                reduced_coefficient=total%13)


if __name__=='__main__':
    assert src.hashlib.sha256(src.SOURCE.read_bytes()).hexdigest().startswith('aa650e28')
    book=json.loads(src.SOURCE.read_text())
    out=[]
    for m,d in [(23,443),(23,491)]:
        z=[coefficient(book,D) for D in (-d,m*d)]
        P2=10*(z[0]['reduced_coefficient']*z[1]['reduced_coefficient'])**2%13
        out.append(dict(m=m,d=d,coefficients=z,squared_toric_residue=P2,
                        possible_residues=[x for x in range(13) if x*x%13==P2]))
    print(json.dumps(out,indent=2,sort_keys=True))
