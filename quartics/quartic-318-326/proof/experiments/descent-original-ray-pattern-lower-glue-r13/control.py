"""Exact rational checks for actual original coarse floors/strips, not analytic estimates."""
from fractions import Fraction as F
from math import isqrt, prod
import random
rng = random.Random(318326)
nsize = nbudget = npower = 0
for W in [1, 2, 3, 6, 30, 210, 2310, 510510]:
    for addN in range(100):
        for addT in range(31):
            N = W * (2000+(11*addN % 19))+addN
            T = W * (200+(7*addT % 11))+addT
            n, m = N//W, T//W - 1
            I = 3*n//4 + 1 - (5*n+7)//8
            assert W*n <= N and W*m <= T and I <= n
            assert F(31,250)*N <= W*I and F(99,100)*T <= W*m
            assert F(3,25)*N*T <= I*m*W*W
            nsize += 1
for _ in range(8000):
    W = rng.randrange(1,2000)
    N = rng.randrange(2000*W,20000*W)
    T = rng.randrange(200*W,N+1)
    n, m = N//W, T//W - 1
    I = 3*n//4+1-(5*n+7)//8
    Z = F(rng.randrange(0,100),23)
    a = F(rng.randrange(0,101),100)
    C = Z*a*W*W*rng.randrange(0,101)/100
    S = max(F(1,1000),6400*Z*W/T)
    k = rng.randrange(0,33)
    eps = S/F(200*max(1,k)*max(1,Z))
    assert Z*k*eps <= S/200 and 6400*Z*W <= S*T
    assert C*k*eps*n*m <= a*S*N*T/200
    assert 16*C*(I+m) <= a*S*N*T/200
    nbudget += 1
def icbrt(x):
    a,b=0,x+1
    while b-a>1:
        c=(a+b)//2
        if c*c*c<=x:a=c
        else:b=c
    return a
for _ in range(8500):
    W=rng.randrange(1,4000); n=rng.randrange(512,10**8); N=W*n+rng.randrange(W)
    d=icbrt(n*n); cut=d+(d*d*d<n*n)       # ceil(n^(2/3)) exact
    assert 2*W < N <= W*(n+1) and 2*W*cut < N
    npower += 1
print(f'{nsize} exact rectangular floor/area; {nbudget} rational dual-budget; {npower} exact cutoff/no-wrap controls PASS')
