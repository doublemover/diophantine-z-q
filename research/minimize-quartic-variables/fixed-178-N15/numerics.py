"""Independent rational/integer guards used to transfer both old contradiction thresholds."""
from fractions import Fraction as F
from math import comb,prod
from itertools import combinations
assert sum(comb(3,j-1) for j in range(1,5))==8
assert sum(comb(3,j-1)*2*(j-1)for j in range(1,5))==24
assert prod(j**comb(3,j-1)for j in range(1,5))==864
rho=F(3,2)
assert 2+2*rho+2+4*rho+2*rho+26+8*rho+4*(3+rho)+1<100
assert 149**66>10**9 and 360*10000*10**9+2500*10000<10**18
assert 3*F(40*10000,9999)<F(12002,100)
# second absorption exempts log33<4; (1-1/10^4)^-2·120 <121
assert 121*9999**2>120*10000**2
assert 484>F(12002,100)*4
print('PASS weighted subset constants, arch coefficient 100, both height budgets')
