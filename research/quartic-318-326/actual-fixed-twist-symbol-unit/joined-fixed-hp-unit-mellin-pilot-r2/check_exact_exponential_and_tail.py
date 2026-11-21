from fractions import Fraction as Q
from math import isqrt, factorial
p,N,h, B, U=415721,205042530,2207,32000000,1000000
def atan(x,N):return sum(((-1)**j*x**(2*j+1)/Q(2*j+1) for j in range(N)),Q(0))
pilo=16*atan(Q(1,5),32)-4*atan(Q(1,239),33)
pihi=16*atan(Q(1,5),33)-4*atan(Q(1,239),32)
# 32 terms ends negative, 33 positive, so bounds by alternating series.
M=10**35
s=isqrt(N*M*M)
l0=2*pilo/(h*Q(s+1,M))
l1=2*pihi/(h*Q(s,M))
L=2**52
r0=1-l1+l1*l1/2-l1*l1*l1/6
r1=1-l0+l0*l0/2
lo=(r0*L).__floor__()
hi=(r1*L).__ceil__()
assert hi-lo<=2
assert l0*U>Q(1988,10000)
t=Q(1988,10000)
assert sum((-t)**j/Q(factorial(j)) for j in range(5))<Q(41,50)
# H_floor(sqrt(B+U))≤1+log(sqrt(B+U))<10.
assert sum(Q(9**j,factorial(j)) for j in range(18))>5745
assert 5745**2>B+U and 5656**2<B and B+U<4*B
C=Q(2*U*10,5656)+4
tail=2*C*Q(41,50)**32/(1-Q(41,50))
assert tail<69
B=64000000
assert sum(Q(9**j,factorial(j)) for j in range(19))>8063
assert 8063**2>B+U and 8000**2==B and B+U<4*B
C=Q(2*U*10,8000)+4
tail64=2*C*Q(41,50)**64/(1-Q(41,50))
assert tail64<Q(85,1000)
assert (p*pilo)**2>100**2*77175*h
print('scale',L)
print('ratio_floor',lo)
print('ratio_ceil',hi)
print('strict_tail_bound_32M',69)
print('strict_tail_bound_64M','0.085')
print('strict_unit_L_limit',100)
