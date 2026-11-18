"""Exact multiquadratic signed-norm polynomial, plus tiny total-space Jacobian examples.
This checks selected initial charts, not the iterated resolution engine.
"""
from itertools import product
from math import prod
from sympy import ZZ,symbols,Poly
from sympy.polys.rings import ring
A,T,X=ring("T,X", ZZ)

def multiply(x,y,fs):
    """Sparse sign-bit basis over any commutative coefficient ring."""
    z={}
    for I,b in x.items():
        for J,c in y.items():
            K=I^J
            z[K]=z.get(K,0)+b*c*prod(f for j,f in enumerate(fs) if I&J&(1<<j))
    return {i:a for i,a in z.items() if a}

def conjugate_norm_polynomial(b,fs):
    """Output product(X-sigma(b)) by quadratic norm down 4 levels."""
    v={i:-a for i,a in b.items()};v[0]=v.get(0,0)+X
    for j in range(3,-1,-1):
        v=multiply(v,{I:(-c if I&(1<<j) else c) for I,c in v.items()},fs)
        assert all(I<(1<<j) for I in v)
    return v[0]

def integral_over_dyadic_parameter(b,fs,n):
    """For integral polynomials on finite Z_(2)[T], test b/2^n exactly."""
    h=conjugate_norm_polynomial(b,fs)
    assert h.get((0,16),0)==1
    return all(c%(2**(n*(16-i)))==0 for (j,i),c in h.items())

def mixed_row(f,args):
    """Entries are integer polynomial lifts; reduce to F2 by the caller."""
    delta=Poly((f.subs({x:x**2 for x in args},simultaneous=True)-f**2)/2,*args,domain=ZZ)
    return [delta.as_expr()]+[f.diff(x)**2 for x in args]

def test():
    # Actual mixed pattern (1,1,2,-2): unlike first three modulo unramified squares.
    fs=[T,T-32,2*(T-76832),-2*(T+343)]
    assert integral_over_dyadic_parameter({1:-1,2:1},fs,1) # (r1-r0)/2
    assert integral_over_dyadic_parameter({12:1},fs,1) # r2*r3/2
    assert not integral_over_dyadic_parameter({4:1},fs,1) # r2/2
    allbits=conjugate_norm_polynomial({3:1,5:1,12:1},fs)
    assert allbits.get((0,16))==1 and allbits!=0
    for e in product(range(2),repeat=4):
        assert sum([e[0]]+[(e[0]+i)%2 for i in e[1:]])<=4
        assert 4+sum(e)<=8
    t,w=symbols('t w')
    # At the origin both special fibres have ordinary derivative zero.
    # The first total space is regular and the second singular.
    for f,expected in [(w*w-2,1),(w*w-2*t,0)]:
        row=mixed_row(f,(t,w))
        assert [int(g.subs({t:0,w:0}))%2 for g in row]==[expected,0,0]
    print("signed norms: two integral half-elements and a nonintegral one; 16 reciprocal parity bounds; two mixed-Jacobian examples: OK")
if __name__=='__main__': test()
