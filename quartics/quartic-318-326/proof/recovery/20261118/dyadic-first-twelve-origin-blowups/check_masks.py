from itertools import product
from sympy import symbols,expand
b=[0,32,76832]
def val(x):
 return (abs(x)&-abs(x)).bit_length()-1
for sig in product((1,-1),repeat=3):
 if len(set(sig))==1:continue
 d=1 if sum(sig)>0 else -1
 j,k=[i for i,v in enumerate(sig) if v==d];m=next(i for i,v in enumerate(sig) if v!=d)
 H=d*(b[j]-b[k])//4;M=d*(b[m]-b[j])//2
 assert val(H)==(8 if j==1 else 3) and val(M)>=4
u,s,C,tau,d=symbols('u s C tau d')
g=(1-d)/2;w=tau+u
assert expand(tau**2-2*(w+C-u*tau-g*u*u)-(w**2-2*w-d*u**2-2*C))==0
print('six majority triples; exact local coefficient orders and tau relation verified')
