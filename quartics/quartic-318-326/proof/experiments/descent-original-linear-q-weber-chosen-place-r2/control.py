from itertools import product
from math import isqrt
def prime(p): return p>=2 and all(p%q for q in range(2,isqrt(p)+1))
signed=kernels=opposite=mods=0
for a,b in product(range(-15,16),repeat=2):
    p=a*a+b*b
    if not prime(p):continue
    signed+=1
    assert a%p and b%p
    j=-a*pow(b%p,-1,p)%p
    assert (j*j+1)%p==0 and (a+b*j)%p==0
    for x,y in product(range(-11,12),repeat=2):
        membership=(x*a+y*b)%p==0 and (y*a-x*b)%p==0
        assert membership==((x+y*j)%p==0)
        kernels+=1
    if p>2:
        assert (a-b*j)%p
        opposite+=1
    for N in range(1,48):
        n=N%p
        assert (n!=0)==(N%p!=0)
        if n:assert n*pow(n,-1,p)%p==1
        mods+=1
print('literal signed norm-p pairs, including p=2:',signed)
print('kernel/principal complex division checks:',kernels)
print('conjugate root distinguishes ideal for odd p:',opposite)
print('prime-to-p residue unit controls:',mods)
