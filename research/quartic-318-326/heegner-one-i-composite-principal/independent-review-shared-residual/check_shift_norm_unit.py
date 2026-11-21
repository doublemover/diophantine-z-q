#!/usr/bin/env python3
"""Independent shift norm unit and opposite 5881 local check."""
from pathlib import Path
from functools import cache
import json
from math import gcd
import sys
from hashlib import sha256
from sympy.polys import galoistools as g
from sympy.polys.domains import ZZ

def read_pinned(path,pin):
    b=Path(path).read_bytes(); assert sha256(b).hexdigest()==pin
    return json.loads(b)
A=read_pinned(sys.argv[1],'8c7d250975747b55a0b07b0c31566b613fd203eb427e16310c0e344ca337f5d0')
N=read_pinned(sys.argv[2],'0fc655687e1eac9a2ef192445eefcbef7d092c16c8e75e8bd7e29a5dd205e3e3')
d=N['d']; expected=N['exact_signed_norm']
for p in (N["remaining_cofactor_unfactored"],):
    def scal(x,z): return tuple(g.gf_mul_ground(list(x),z,p,ZZ))
    F=tuple(int(c//26**k)%p for k,c in enumerate(A['actual_line_polynomial_desc']))
    assert all(c%26**i==0 for i,c in enumerate(A['actual_line_polynomial_desc']))
    def add(a,b): return tuple(g.gf_add(list(a),list(b),p,ZZ))
    def mul(a,b): return tuple(g.gf_rem(g.gf_mul(list(a),list(b),p,ZZ), list(F),p,ZZ))
    co=[]
    for pc in A['relative_monic_x_coeffs_ascending_num_den']:
        u=(); power=(1,)
        for a,b in pc:
            u=add(u,scal(power,a*pow(b,-1,p)%p))
            power=mul(power,(26,0))
        co.append(u)
    P=[*(scal(v,-1) for v in reversed(co)),(1,)]
    def shift(v): return tuple(add(x,mul(v[-1],y)) for x,y in zip(((),*v[:-1]),P))
    # alpha*sigma(alpha) = 169^2 B^2 - 13*d*v*(v-13)*(v+39).
    d0=3*5881
    a=add(scal((1,0,0),169**2),((2*d0*169)%p,d0*d0%p))
    w=(a,(13*d*13*39%p,),(-13*d*26%p,),(-13*d%p,),(),())
    cols=[w]
    for _ in range(5):cols.append(shift(cols[-1]))
    @cache
    def det(mask):
        if not mask:return (1,)
        j=6-mask.bit_count();w=()
        for k,i in enumerate(i for i in range(6) if mask&(1<<i)):
            a=mul(cols[j][i],det(mask^(1<<i)))
            w=add(w,scal(a,-1) if k&1 else a)
        return w
    z=det(63)
    # Determinant of multiplication by z over Fp[B].
    def pad(x): return list(reversed(x))+[0]*(14-len(x))
    c=[]; x=z
    for i in range(14):
        c.append(pad(x));x=mul(x,(1,0))
    M=list(map(list,zip(*c))); D=1
    for i in range(14):
        j=next((j for j in range(i,14) if gcd(M[j][i],p)==1),None)
        if j is None:D=0;break
        if i!=j:M[i],M[j]=M[j],M[i];D=-D
        a=M[i][i]%p;D=D*a%p
        ia=pow(a,-1,p)
        for r in range(i+1,14):
            t=M[r][i]*ia%p
            M[r][i:]=[(x-t*y)%p for x,y in zip(M[r][i:],M[i][i:])]

    assert gcd(D,p)==1
    print("unit determinant modulo literal composite C",len(str(p)))

R=read_pinned(sys.argv[3],'9d630105a584882ea6a18171075ee0c1e8a6ec680a840aa1ce7c8286052b3f11')
G=read_pinned(sys.argv[4],'7b2e1a705f472777e347e6b40c1b10074b7a25035ba7dcd4ef8a771aaf0c458a')

l=5881; lm=l*l
u=R['r_5881_opposite_root_u_mod_p2']
W=R['r_5881_opposite_root_W_mod_p2']
assert G['d']==d==R['actual_d'] and R['denominator']==3*l
t=u; b=0
for _ in range(6):
    b=(b+t)%lm
    t=((3*t*t+4*t-3)**2 * pow(4*t*(t-1)*(t+3),-1,lm) - 2-2*t)%lm
assert u==t
B=b*pow(2,-1,lm)%lm
assert B==R['r_5881_opposite_B_mod_p2'] and W%l==(-3360)%l and u%l==2185
z=0
for f in G['x_root_poly_coefficients']: z=(z*u+f)%lm
assert z==0
v=13*u%lm
assert (W*W-13*d*v*(v-13)*(v+39))%lm==0
n=(W+169*B)%lm
assert n//l==R['r_5881_opposite_cancellation_witness'] and n%l==0
assert (1+(n//l)*pow(3,-1,l))%l==R['r_5881_opposite_residue_unit']==2406
V={int(k):t for k,t in N['nonformal_3_valuations_by_scalars'].items()}
Z={str(k):V[13-k]-13 for k in range(1,13)}
assert Z==R['r_nonformal_3_valuations_by_scalars']
assert sum(t*pow(int(k),-1,13) for k,t in Z.items())*pow(12,-1,13)%13==2
print('opposite 5881 unit 2406, projected 3 coordinate 2 (basis coefficient -2)')
