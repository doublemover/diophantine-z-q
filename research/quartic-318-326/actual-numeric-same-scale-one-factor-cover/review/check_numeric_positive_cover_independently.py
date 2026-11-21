#!/usr/bin/env python3
"""Independent mod-p² formal/affine, Lucas, CRT and rational conic check.

Derives each of the four point orders directly from asserted minimality
and certified integer factorization. Does not take Gaussian CM counts as
point orders or use the author's formal or Lucas binary index helper.
The heavy separate outward real interval is checked by the author replay.
"""
from fractions import Fraction as F
from math import gcd, isqrt, lcm, prod
from pathlib import Path
from functools import lru_cache
import argparse, json
pa=argparse.ArgumentParser()
pa.add_argument('numeric')
pa.add_argument('joined_dir')
args=pa.parse_args()
rows=json.loads(Path(args.numeric).read_bytes()); b=rows['b']
Q=(F(1,2399), F(-1,2), F(-1), F(-32,407), F(0))
def vp(x,p):
    x=F(x)
    if not x:return 2**63
    a,d=x.numerator,x.denominator
    v=0
    while not a%p:a//=p; v+=1
    while not d%p:d//=p; v-=1
    return v
def red(x,m):
    x=F(x)
    return x.numerator*pow(x.denominator,-1,m)%m
def prime(p):return p>1 and all(p%k for k in range(2,isqrt(p)+1))
def chi(x,p):
    a=pow(red(x,p),(p-1)//2,p)
    return -1 if a==p-1 else a
def M(A,B,m):
    a,b,c,d = A
    e,f,g,h = B
    return ((a*e+b*g)%m,(a*f+b*h)%m,(c*e+d*g)%m,(c*f+d*h)%m)
def mpow(s,n,m):
    A=(0,1,m-1,s%m)
    P=(1,0,0,1)
    while n:
        if n&1:P=M(P,A,m)
        A=M(A,A,m); n>>=1
    return P
def group(p,r):
    m=p*p
    D=(3-r)**2%m
    assert gcd(2*D,p)==1 and r*r%m==2
    R=((1+r)%m,2*r%m)
    O=(0,)
    assert (R[1]**2-R[0]**3+D*R[0])%m==0
    def recip(a):return pow(a,-1,m)
    def add(P,Q):
        if len(P)==1:
            if len(Q)==1:return ((P[0]+Q[0])%m,)
            z,x,y=P[0],*Q
            return ((x+2*y*z)%m,(y+(3*x*x-D)*z)%m)
        if len(Q)==1:return add(Q,P)
        x,y=P; X,Y=Q
        if (X-x)%p:
            l=(Y-y)*recip(X-x)%m
        elif (Y-y)%p:
            # Antipodal reductions with y not zero; local inverse slope.
            return ((X-x)*recip(Y-y)%m,)
        else:
            H=X*X+X*x+x*x-D
            if (Y+y)%p:
                # Removable affine slope singularity, including doubling.
                l=H*recip(Y+y)%m
            else:
                # Common nonzero two-torsion reduction. Smoothness makes H a
                # unit. z=-x/y is inverse slope modulo p² on the formal disk.
                return ((Y+y)*recip(H)%m,)
        Z=(l*l-x-X)%m
        V=(l*(x-Z)-y)%m
        assert (V*V-Z**3+D*Z)%m==0
        return Z,V
    def point(n):
        P=O; B=R
        while n:
            if n&1:P=add(P,B)
            B=add(B,B); n>>=1
        return P
    def func(P):
        if len(P)==1:return -2*P[0]%m
        x,y=P
        return 2*y*recip(x*x+D)%m
    return point,func
def contacts(path):
    p=Path(path)
    files=(
       'linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json',
       'linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json',
       'linked-detector-twelve-compatible-incidences-r1/EXACT-TWELVE-INCIDENCES.json',
       'linked-detector-low-opposite-unhit-r1/EXACT-LOW-OPPOSITE-NEW-CLASS.json',
       'linked-detector-gaussian-order29-new-classes-r1/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json')
    d=[json.loads((p/a).read_bytes()) for a in files]
    data={t['prime']:(t['scales_mod_p2'][1]*t['r_over_d_mod_p2'])%t['prime']**2 for dd in d for t in dd['rows']}
    return data,d[-1]
S,old=contacts(args.joined_dir)
h0,L0=int(old['simultaneous_h_residue']),int(old['simultaneous_h_modulus'])
assert int(old['literal_scalar_J'])==int(rows['literal_J']) and rows['h_prefix']==h0 and rows['h_prefix_modulus']==L0
s=1+6**15*3**65536*int(rows['literal_J'])
den=s-2; k=2*den
h=rows['final_h']; H=rows['h_modulus']
assert h%L0==h0 and h.bit_length()==2648
new=rows['actual_new_contacts']; rprime=[r['p'] for r in new]
assert prod(rprime)==b and len(S)==16 and gcd(prod(S),b)==1
assert chi(rprime[0],rprime[1])==1
tables=[]
for row in new:
    p=row['p']; m=p*p
    assert p>76176 and prime(p) and p%8==1
    assert [chi(p,r) for r in (3,5,7,11,37,2399)]==[1,1,-1,1,-1,1]
    assert gcd(prod(row['arm_counts']),prod(S)*b//p)==1
    A=[]
    for ix,arm in enumerate(row['arms']):
        o=arm['order']
        factors=arm['order_factorization']
        assert prod(l**e for l,e in factors)==o
        assert all(prime(l) for l,e in factors)
        r=arm['r_p2']; assert r%p==arm['r']
        assert (r*r-2)%m==0
        order,fn=group(p,r)
        pp=order(o); assert len(pp)==1 and vp(pp[0],p)==1 and pp[0]==arm['first_formal_z']
        assert all(len(order(o//l))==2 for l,e in factors)
        assert h%o==ix and h%p**4==p**3
        N=p*o
        g=1
        for l in [p,*[l for l,e in factors]]:
            g*=l**vp(den,l)
        Bmat=mpow(s,k,N*g)
        xx,yy=Bmat[1],Bmat[3]
        assert xx%g==0
        Z=[3723%N,s%N,yy%N,((xx//g)*pow(den//g,-1,N))%N]
        assert Z==arm['labels']
        now=[fn(order(z)) for z in Z]
        assert now==arm['U_p2']
        a=pow(prod(now)%m,-1,m)
        assert a==arm['product']; A.append(a)
    assert row['arms'][1]['r']==p-row['arms'][0]['r']
    cs=[1, ((A[0]+A[1])*pow(2,-1,m)+prod(A))%m,prod(A)%m]
    assert cs==row['c_mod_p2'] and all(c%p for c in cs)
    expected=lcm(L0,p**4,*[r['arms'][i]['order'] for r in new for i in range(2)],*[r['p']**4 for r in new])
    assert H==expected and 0<h<H and rows['h_step']==0
    root=row['exact_W_target']; w=row['w_mod_p2']
    assert (root-cs[1]*w)%m==0 and red(root*root-Q[0],m)==b%m
    tt=[(c*w)**2%m for c in cs]
    fs=[prod((t-red(z,m))%m for z in Q)%m for t in tt]
    assert row['T_rows']==tt and row['F_rows']==fs
    assert len({(red(z,p)*pow(c,-2,p))%p for z in Q[:-1] for c in cs})==12
    assert all(fs[i]%p for i in (0,2)) and fs[1]%p==0 and fs[1] and tt[1]%p!=1
    tables.append((p,fs[1]//p))
    S[p]=root
ww,yy=(F(*rows[k]) for k in ('actual_scaled_pair_W','actual_scaled_pair_Y'))
U,V=rows['chosen_global_param']; X,Y,Z=rows['base_ternary_triple']
assert X*X-b*Y*Y==2399*Z*Z and Y==1 and ww*ww-b*yy*yy==Q[0] and ww>2
for r,(p,depth,x,y) in enumerate(rows['local_parameter_residues']):
    assert (U-x)%p**depth==0 and (V-y)%p**depth==0
# Direct multiplication of norm-one factor by seed in Q(sqrt b).
A=F(V*V+b*U*U,V*V-b*U*U)
B=F(2*U*V,V*V-b*U*U)
assert A*A-b*B*B==1
assert (A*X+b*B, A+B*X)==(ww*(2399*Z),yy*(2399*Z))
assert dict(rows['all_W_target_p2'])==S and all(red(ww,p*p)==v for p,v in S.items())
depths={str(p):vp(ww,p) for p in (2,3,5,7,11,17,37,2399)}
assert depths==rows['fixed_pair_bad_W_depths'] and max(depths.values())<=-5
assert all(vp(ww**2-Q[0],p)==1 and vp(yy,p)==0 for p in rprime)
assert chi(b,23)==-1 and vp(ww,23)>=0
print(json.dumps(dict(new_exact_odd_support=rprime,middle_unnormalized_P_over_p=tables,old_W_cells=len(S)-len(new),
  h_bitlength=h.bit_length(),fixed_W_depths=depths, nonsquare_at=23, W_gt_2=True),indent=2))
