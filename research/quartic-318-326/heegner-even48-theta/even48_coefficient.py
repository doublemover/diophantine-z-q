#!/usr/bin/env python3
"""Compute the level-48 ST theta coefficient from the actual 4-class packet.

The simple bounded representation enumeration is for examples.  No claim
of practicality at 68-digit target twists.
"""
import argparse
import itertools
import json
from math import isqrt
from even48_brandt import key, reps, transform, emit


def disc(v):
    b,c,d = v
    return -3*b*b-4*(c*c-c*d+d*d)


def add3(x,y):
    return tuple(a+b for a,b in zip(x,y))


def leg(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)


Z19=next(z for z in itertools.product(range(19),repeat=3) if any(z) and disc(z)%19==0)
Z19_index=next(j for j in range(3) if Z19[j])
Z19_inv=pow(Z19[Z19_index],-1,19)


def weight19(v):
    vp=tuple(a%19 for a in v)
    if not any(vp) or disc(v)%19:
        return 0
    beta=(disc(add3(v,Z19))-disc(v)-disc(Z19))%19
    if beta:
        return leg(-beta,19)
    a=vp[Z19_index]*Z19_inv%19
    assert a and all(vp[j]==a*Z19[j]%19 for j in range(3))
    return leg(a,19)


def reps_at_discriminant(D):
    M=19*D
    for b in range(-isqrt(M//3),isqrt(M//3)+1):
        rem=M-3*b*b
        if rem%4:
            continue
        for d in range(-isqrt(rem//3),isqrt(rem//3)+1):
            r=rem-3*d*d
            s=isqrt(r)
            if s*s!=r:
                continue
            for v in ((s,-s) if s else (s,)):
                if (d+v)%2==0:
                    c=(d+v)//2
                    y=(b,c,d)
                    assert disc(y)==-M
                    yield y


def coefficient(D):
    assert D>0 and D%24==13
    vals=[0]*len(reps)
    total_nz=[0]*len(reps)
    n=0
    for v in reps_at_discriminant(D):
        n+=1
        w=leg(v[1]+v[2],3)*weight19(v)
        if not w:
            continue
        q=(0,*v)
        for i,line in enumerate(reps):
            # This integral quaternion need not be a unit at 2.  A
            # nonprimitive image still preserves the line exactly when
            # the column determinant vanishes modulo 16.
            from even48_brandt import ev
            wv=ev(q,line)
            if (line[0]*wv[1]-line[1]*wv[0])%16==0:
                vals[i]+=w
                total_nz[i]+=1
    f=emit()["primitive_eigenfunction"]
    return dict(D=D, representation_count_maximal_order=n,
                weight19_auxiliary=Z19, nonzero_weights_by_class=total_nz,
                weighted_sums_by_class=vals,
                coefficient=sum(a*b for a,b in zip(vals,f)))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("D",type=int,nargs="+")
    args=p.parse_args()
    print(json.dumps([coefficient(D) for D in args.D],indent=2,sort_keys=True))
