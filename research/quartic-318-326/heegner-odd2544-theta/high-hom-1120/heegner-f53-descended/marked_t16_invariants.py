#!/usr/bin/env python3
"""Exact t4/t8/t16 from distinguished subgroup; no search over unoriented j."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'heegner-f53-oriented'))
import oriented_projection as D8

def t4(A,P4):
    x0=A.mul(2,P4)[0]
    v=P4[0]-x0
    assert v*v==3*x0*x0+A.A
    k=3*x0/v
    return 64/(k-2)

def t8(A,P8):
    x0=A.mul(4,P8)[0]
    v=A.mul(2,P8)[0]-x0
    S=P8[0]+A.mul(3,P8)[0]-2*x0
    s=S/v
    return 32/(s-6)

def t16(A,P16):
    source=t8(A,A.mul(2,P16))
    B,f=A.quotient(A.mul(8,P16),2)
    dest=t8(B,f(P16))
    x=(dest-2*source)/(source+4)
    assert x*x==source*(x+2) and x*(x+4)==dest
    return x

def t3(A,P3):
    x,y=P3
    slope=(3*x*x+A.A)/(2*y)
    assert slope*slope==3*x
    k=4*slope**3/y
    return 729/(k-27)

if __name__=='__main__':
    g16,g3=D8.generator(16,2),D8.generator(3,3)
    C,f=D8.E0.quotient(g3,3)
    for A,P in [(D8.E0,g16),(C,f(g16))]:
        assert t16(A,P)==D8.haupt(D8.edges(A,P,4))
    assert t3(D8.E0,g3)==-27*D8.one
    print('Exact marked t16, both independent projections, and marked t3 pass.')
