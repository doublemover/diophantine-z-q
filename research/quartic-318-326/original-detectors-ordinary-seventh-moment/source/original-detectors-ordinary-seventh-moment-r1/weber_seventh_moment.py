#!/usr/bin/env python3
"""Evaluate exact monic reciprocal-Weber jets over F_2; no CM authentication."""
import argparse
import json
import sys

def leading_jet(poly):
    assert poly>0
    n=poly.bit_length()-1
    return [poly>>(n-i)&1 if i<=n else 0 for i in range(8)]

def product(A,B):
    assert len(A)==len(B)==8 and A[0]==B[0]==1
    D=[0]*8
    for i,a in enumerate(A):
        for j,b in enumerate(B[:8-i]):
            D[i+j]^=a&b
    return D

def powers(A):
    assert len(A)==8 and A[0]==1 and set(A)<={0,1}
    P=[0]*8
    for k in range(1,8):
        t=(k&1)&A[k]
        for i in range(1,k):
            t^=A[i]&P[k-i]
        P[k]=t
    return P[1:]

def consume(rows):
    J=[1]+[0]*7
    for A in rows:
        J=product(J,A)
    P=powers(J)
    return {"jet":J,"power_sums":P,"phase":P[6],
            "simplified_phase":J[7]^(J[2]&J[5]) if not (J[1] or J[3]) else None}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--polynomials',action='store_true',
        help='parse one binary-polynomial bit mask in Python integer syntax per line')
    args=p.parse_args()
    rows=(line.strip() for line in sys.stdin)
    jet=(leading_jet(int(s,0)) if args.polynomials else json.loads(s) for s in rows if s)
    print(json.dumps(consume(jet),sort_keys=True))
if __name__=='__main__':main()
