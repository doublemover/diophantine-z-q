from itertools import product
V=list(product(range(3),repeat=4))
mod=lambda x:tuple(a%3 for a in x)
def red(a):return mod((a[0]-a[2],a[1]-a[3],-a[2],a[3]))
def inv(x):return mod((x[0]-x[2],x[1]+x[3],-x[2],x[3]))
def orig(a,b):
 x,y,z,w=a;r,s,t,u=b
 return mod((x*r-210*y*s-84*y*u+z*t-126*w*s-42*w*u,
 x*s+y*r-2*y*t+3*z*s+z*u-w*t,
 x*t+z*r-42*y*u+z*t+42*w*s,
 x*u+w*r+5*y*t-5*z*s-2*z*u+3*w*t))
def mul(a,b):
 r,i,j,k=a;s,l,m,n=b
 return mod((r*s+2*j*m,r*l+i*s-2*j*n+2*k*m,r*m+j*s,r*n+i*m-j*l+k*s))
for a in V:
 assert inv(red(a))==a
 assert (red(a)==(0,0,0,0)) == all(x==0 for x in a)
 for b in V:assert red(orig(a,b))==mul(red(a),red(b))
rad=[a for a in V if a[0]==a[2]==0]
assert len(rad)==9
assert all(mul(a,b)==(0,0,0,0) for a in rad for b in rad)
units=[a for a in V if any(mul(a,b)==(1,0,0,0) and mul(b,a)==(1,0,0,0) for b in V)]
assert len(units)==72
assert all(a in units for a in V if a not in rad)
assert len({min(a,mod(-x for x in a)) for a in units})==36
assert all((r*r-2)%3 for r in range(3))
print('PASS: literal order multiplication, all6561 reductions,81 coordinate inverses, full square-zero radical, F9 and72/36 actual unit/sign counts')
