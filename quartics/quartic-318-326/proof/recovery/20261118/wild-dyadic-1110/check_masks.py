"""Check closed-fibre residue labels and exact polynomial identities, not a proof of regularity."""
from itertools import product
from sympy import symbols,expand
u,h,k,w,x,W,d,t,p=symbols('u h k w x W d t p')
L=(u+1)*w+u**2+u-171
assert expand((u+w+1)**2+u**2-343-(w*w+2*L))==0
J=(1+x)*W+1+x-171*x*x
assert expand((1+x+W)**2+1-343*x*x-(W*W+2*J))==0
for a in (8,19208):
 assert expand((u+2*h)**2-(u*u+4*a)-4*(h*h+u*h-a))==0
assert expand((d-2400)*(d-2400+t+4800)+2400*2401-(d*d+t*d-2400*(t-1)))==0
assert 2400==75*32 and 4*19208==76832 and 8*2401==19208
def mul(a,b): # F4 = F2[z]/(z²+z+1)
 c=(a if b&1 else 0) ^ ((a<<1) if b&2 else 0)
 return c^7 if c&4 else c
labs={(v,i,j) for v,i,j in product(range(4),repeat=3) if mul(v,v)^v^1==0 and mul(i,i^v)==mul(j,j^v)==0}
frob=lambda xyz:tuple(mul(y,y) for y in xyz)
orbs={frozenset((z,frob(z))) for z in labs}
assert len(labs)==8 and len(orbs)==4 and all(len(o)==2 for o in orbs)
print('finite/reciprocal identities; four degree-two closed nodes; integer split constants: OK')
