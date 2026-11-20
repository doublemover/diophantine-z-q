#!/usr/bin/env python3
"""Exact shorter auxiliary twists on the same 416 marked p53 labels and λ."""
import json
from itertools import product
from math import prod,isqrt
import sys
from check_negative_small import src,new_reps


def primes_of(q):
    assert q>0
    a=[]
    for p in range(2,isqrt(q)+1):
        if not q%p:
            q//=p
            assert q%p
            a.append(p)
        if p>q:break
    if q>1:a.append(q)
    return a

def coeff(book,D,l, enumerator=new_reps):
    neg=D<0
    W=tuple(primes_of(abs(l)))
    assert prod(W)==abs(l) and all(p not in (2,3,29,53) for p in W)
    M=-l*D
    assert M>0 and M%8==7 and M%3==2 and M%53!=0
    assert src.leg(l,53) == (1 if neg else -1)
    assert src.leg(l,3) == 1 and l%8==5
    mm={int(v):src.matrix_mod_factory(A,int(v)) for v,A in book['exact_level_matrices'].items()}
    t0=next(x for x in range(1,53) if (M-3*x*x)%53==0) if neg else None
    out=[]
    for cls in book['marked_classes']:
        den=cls['basis_denominator']
        addr={tuple(tuple(v) for v in row['inverse_transport_mark']):row['lambda13_phi0']
              for row in cls['exact_marks']}
        total=0
        for v in enumerator(cls['max_order_basis_columns'],den,M):
            a=1 if den==1 else src.leg(l,29)
            for r in W:
                a*=src.wtI(v,den,r)
                if not a:break
            if not a:continue
            if neg:
                t=(3*v[0]+2*v[1]-v[2])*pow(3*den,-1,53)%53
                assert t in (t0,53-t0)
                if t!=t0:a=-a
            vv16=mm[16](tuple(x%16 for x in v),den)
            vv3=mm[3](tuple(x%3 for x in v),den)
            m16=src.marked_values(vv16,16,2)
            m3=src.marked_values(vv3,3,3)
            for x,y in product(m16,m3):
                total+=a*addr.get((x,y),0)*src.leg(2*m3[y]-vv3[0]-vv3[-1],3)
        out.append(total)
    return dict(D=D,aux_l=l,typeI_primes=W,disc_magnitude=M,phase_coordinate=t0,
        raw_mod13_representatives_by_class=out,coefficient_mod13=sum(out)%13)

def main():
    book=json.loads(src.SOURCE.read_text())
    assert src.hashlib.sha256(src.SOURCE.read_bytes()).hexdigest().startswith('aa650e28')
    if len(sys.argv)>2:
        print(json.dumps([coeff(book,int(D),int(l)) for D,l in
                          zip(sys.argv[2::2],sys.argv[3::2])],indent=2,sort_keys=True))
        return
    data={}
    for D,l,label in ((37,-323,'first_positive_aux_seed'),(-35,37,'first_negative_aux_seed'),
                      (-323,37,'reference_negative'),(146965,-35,'reference_positive')):
        data[label]=coeff(book,D,l)
    a=data['reference_negative']['coefficient_mod13']
    b=data['reference_positive']['coefficient_mod13']
    data['ref_signed_13_projection']=11
    data['ref_square']=121%13
    data['calibrated_multiplier_mod13']=data['ref_square']*pow((a*b)**2,-1,13)%13
    print(json.dumps(data,indent=2,sort_keys=True))
if __name__=="__main__":main()
