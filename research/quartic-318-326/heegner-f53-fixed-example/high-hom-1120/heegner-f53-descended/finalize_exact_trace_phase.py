#!/usr/bin/env python3
"""Recheck all case sums and use the exact common Weil-normalized Gauss root."""
import argparse,hashlib,json
from pathlib import Path
from one_class_weighted_trace import D8,D16,D18,E,p,read,parse,short,long,dump_k,leg

def gauss(M,root,m,k):
    a=M.F(tuple(root))**k
    z=a**0
    assert a!=z and a**m==z
    S=M.zero
    for i in range(1,m):
        z=z*a
        S+=leg(i,m)*z
    assert S*S==M.F.of(m if m%4==1 else -m)
    return S.subfield()
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("packet",type=Path)
    f=ap.parse_args().packet
    P=json.loads(f.read_text())
    C=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    d=P['cases']
    assert len(d)==20 and len(set(tuple(c['relative_label']) for c in d))==20
    assert P['retained_signed_rows']==5760
    across=None
    for C0 in d:
        S=None;r=C0['rows']
        assert len(r)==288 and set((T['a17'],T['a19']) for T in r)=={(a,b) for a in range(1,17) for b in range(1,19)}
        for T in r:
            w=leg(T['a17'],17)*leg(T['a19'],19)
            assert T['w']==w
            q0=short(tuple(parse(D8,T['phi']))) if T['phi'] else None
            assert C.contains(q0)
            S=C.add(S,C.mul(w,q0))
        assert dump_k(long(S))==C0['weighted_raw_value']
        across=C.add(across,S)
    G17=gauss(D16,P['common_phase17_field16'],17,19)
    G19=gauss(D18,P['common_phase19_field18'],19,17)
    s=read(D8,G17)*read(D8,G19)
    assert s*s==D8.F.of(-323)
    assert dump_k(long(across))==P['raw_sum']
    tau=lambda q:(-323*q[0],s**3*q[1]) if q else None
    T=tau(long(across)); T13=tau(long(C.mul(224,across)))
    if T:
        x,y=T
        assert y*y==x*(x-323)*(x+3*323) and x**p==x and y**p==y
    if T13:
        assert C.mul(13,C.mul(224,across)) is None
    print(json.dumps({
      'incoming_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),
      'classes':20,'each_nonzero_unit_branches':288,'sum_of_a_weights':[sum(x['w'] for x in c['rows']) for c in d],
      'gauss17':G17,'gauss19':G19,'gauss_minus323':s.subfield(),
      'sum_raw':dump_k(long(across)),'actual_E323_trace_residue':dump_k(T),
      'actual_E323_prime13_detector':dump_k(T13),
    },indent=2,sort_keys=True))
if __name__=='__main__':main()
