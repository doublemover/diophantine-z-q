#!/usr/bin/env python3
"""Exact independent rational/Gaussian controls of full projected map."""
from itertools import product
from fractions import Fraction as Q
import json


def mul(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def neg(a):
    return (-a[0],-a[1])


def mm(a, b):
    return tuple(tuple(sum(x*y for x,y in zip(r,c)) for c in zip(*b)) for r in a)


def matvec(m, v):
    return tuple(add(*(mul((x,0), y) for x,y in zip(r,v))) for r in m)


tau_values=((Q(2,7),Q(5,7)),(Q(-1,3),Q(11,2)),(Q(5),Q(1)))
count=0
for nu in (((0,1),(-Q(1,210),0)),((3,4),(-2,7))):
    J=((0,-1),(1,0))
    for a,b,c,d in product((-2,0,1,3),repeat=4):
        beta=((a,b),(c,d))
        M=mm(nu,beta)
        Av=(-M[1][1],M[0][1])
        Bv=(M[1][0],-M[0][0])
        for tau in tau_values:
            projected=tuple(add((z,0), neg(mul(tau,(w,0)))) for z,w in zip(Av,Bv))
            w=(add(mul(tau,(a,0)),(b,0)),add(mul(tau,(c,0)),(d,0)))
            assert projected==matvec(mm(J,nu),w)
            # Independent representative gauge in the periods (tau*u,u).
            u=((Q(a,3),b),(Q(c,7),d))
            A1=tuple(add((z,0),mul(tau,r)) for z,r in zip(Av,u))
            B1=tuple(add((z,0),r) for z,r in zip(Bv,u))
            assert projected==tuple(add(z,neg(mul(tau,w))) for z,w in zip(A1,B1))
            count+=1
print(json.dumps(dict(signed_projection_checks=count,tau_controls=len(tau_values)),
                 indent=2,sort_keys=True))
