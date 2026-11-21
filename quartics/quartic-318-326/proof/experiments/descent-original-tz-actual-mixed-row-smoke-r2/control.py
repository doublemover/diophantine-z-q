#!/usr/bin/env python3
from fractions import Fraction as Q
from itertools import product
from math import prod

trials = points = margins = 0
for k,n,L,W,K in product(range(1,6), [3,7,16,17], [1,2,5], [2,30], [Q(1),Q(35,9),Q(8)]):
    for j in range(k):
        row = Q(0)
        normalized = Q(0)
        for x,m in product(range(1,n+1),range(1,L+1)):
            t = {i:(x+(W*i-i*i-4)*m*m+(i-3)*m+7-1)%n+1 for i in range(k)}
            f = {i:Q((7*t[i]+i)%9,3) for i in range(k)}
            mu = {i:Q((t[i]+i)%6,5) for i in range(k)}
            nu = {i:Q((7*t[i]+i)%9,3)/K+Q(t[i] % 3,10) for i in range(k)}
            dummy = int(5*n<=8*x and 4*x<=3*n)
            factors = [f[i]-mu[i] if i == j else f[i] if i<j else mu[i] for i in range(k)]
            lifted = [u/K for u in factors]
            assert 0 <= dummy <= 1
            assert all(abs(u)<=nu[i]+1 for i,u in enumerate(lifted))
            raw = dummy*prod(factors)
            norm = dummy*prod(lifted)
            assert raw == K**k * norm
            row += raw
            normalized += norm
            points += 1
        normalized /= n*L
        assert normalized == row/(K**k*n*L)
        for eps in [Q(1,100),Q(1,10),Q(1)]:
            assert (abs(normalized)<=eps/K**k) == (abs(row)<=eps*n*L)
            margins += 1
        trials += 1
print('literal exact row/point/threshold controls:',trials,points,margins)
