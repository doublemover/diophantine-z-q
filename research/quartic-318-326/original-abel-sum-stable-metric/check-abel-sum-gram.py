#!/usr/bin/env python3
"""Check the ordered expansion and exact combinatorial factor on finite measures."""
from itertools import permutations, product
from math import factorial, prod
from random import Random
import sympy as s

rng = Random(318326)
for n in range(13):
    assert s.I**(n*n) == s.I**n * (-1)**(n*(n-1)//2)

def sign(p):
    return (-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))

cases = 0
for n in range(5):
    perms=list(permutations(range(n)))
    for _ in range(6):
        m = n+1
        w = [rng.randrange(1,4) for _ in range(m)]
        f = [[rng.randrange(-3,4)+s.I*rng.randrange(-3,4) for _ in range(m)]
             for __ in range(n)]
        G = s.Matrix(n,n,lambda i,j:s.expand(sum(w[k]*s.conjugate(f[i][k])*f[j][k] for k in range(m))))
        baseline=factorial(n)*G.det()
        permutation=s.expand(sum(sign(p)*sign(q)*prod(G[p[k],q[k]] for k in range(n))
                                 for p in perms for q in perms))
        # Tuples with repeated locations give zero determinant; use one
        # ordering and the exact number of orderings for the discrete integral.
        def mass(xs):
            mat=s.Matrix(n,n,lambda i,k:f[i][xs[k]])
            dd=s.expand(mat.det())
            return prod(w[k] for k in xs)*s.expand(s.conjugate(dd)*dd)
        tuples=product(range(m),repeat=n)
        integrand=s.expand(sum(mass(xs) for xs in tuples if len(set(xs))==n))
        assert s.expand(permutation-baseline)==0
        assert s.expand(integrand-baseline)==0
        cases+=1
print(f"PASS: orientation 0..12, and {cases} exact conjugate-first Gram/product-integral controls")
