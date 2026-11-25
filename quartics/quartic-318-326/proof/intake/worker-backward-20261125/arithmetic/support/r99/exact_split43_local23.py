#!/usr/bin/env python3
"""Exact local arithmetic controls on the retained original split-43 tuple."""
from fractions import Fraction as Q

def f4_mul(x,y):
    z=0
    while y:
        if y&1: z^=x
        x*=2
        if x&4:x^=7
        y//=2
    return z
def f4_pow(x,n):
    a=1
    for _ in range(n):a=f4_mul(a,x)
    return a
def order(a,p):
    z,n=a%p,1
    while z!=1:z=z*a%p;n+=1
    return n
def vp(n,p):
    assert n
    d=0
    while n%p==0:n//=p;d+=1
    return d
def ratval(f,p): return vp(f.numerator,p)-vp(f.denominator,p)

assert [x for x in range(4) if f4_pow(x,4)^x==0]==list(range(4))
assert all(sum(f4_pow(y,2)^y==f4_pow(x,3)^1 for y in range(4))==2 for x in range(4))
assert order(-2,11)==5 and order(-3,11)==10 and pow(-3,5,11)==10
q3=[-739600,116487,-5160,0,3]
assert [(i,vp(c,3)) for i,c in enumerate(q3) if c]==[(0,0),(1,2),(2,1),(4,1)]
a=Q(-1,4); assert 3*a<a+vp(860,3) and 3*a<vp(38829,3)
yd=3*a/2; assert yd==Q(-3,8) and 4*2*yd==-3
B=Q(1849,206524416000)
assert [ratval(B,p) for p in (2,3)]==[-15,-1]
assert [ratval(B/210,p) for p in (2,3)]==[-16,-2]
assert all(vp(n,p)==0 for p in (2,3) for n in (1849,14749))
print("split-43 exact: F4 four x roots and two y lifts each; Frobenius orders (5,10);")
print("actual level-three Newton slope +1/4 at p=3, exact d valuation -3 on L3;")
print("raw valuations (-15,-1), primitive (-16,-2); both good-wedge sections units.")
