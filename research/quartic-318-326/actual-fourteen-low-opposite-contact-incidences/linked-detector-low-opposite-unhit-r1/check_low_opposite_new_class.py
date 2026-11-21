#!/usr/bin/env python3
"""Reverse true quotient divisibility at orders 19 and 23 to hit one untouched original class."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import json, runpy
root=Path(__file__).resolve().parent.parent
def pin(rel, digest):
    f=root/rel
    assert sha256(f.read_bytes()).hexdigest()==digest
    return f
def run(rel,digest):
    with redirect_stdout(StringIO()):
        return runpy.run_path(str(pin(rel,digest)))
def read(rel,digest):
    return json.loads(pin(rel,digest).read_bytes())

F=run('linked-detector-w37-depth-r1/check_actual_shallow_formal.py',
      '4302feb27fa532f4e713e512a819c88c975a02993782f4ab9b346b590724ed63')['field']
old=read('rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json',
         '5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7')
u1=read('linked-detector-new-split-singleton-r1/EXACT-SINGLETON-RETUNE.json',
        'd6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c')
h0=int(old['h']); L=int(u1['preserved_old_modulus'])
J=int(old['J']); i=6**15*3**65536*J
assert i%h0==0 and L%int(old['h_CRT_step'])==0
assert L%64==h0%64==0
s=1+i; k=2*(s-2); bits=bin(k)[2:]
def lucas2(N):
    # If (x,y)=(U_n,U_(n+1)), the pair for 2n is
    # (x(2y-sx), y^2-x^2); odd follows the exact recurrence.
    x,y=0,1; a=s%N
    for bit in bits:
        T=x*(2*y-a*x)%N
        U=(y*y-x*x)%N
        if bit=='0':x,y=T,U
        else:x,y=U,(a*U-T)%N
    return x,y
def prime_factors(n):
    p=2
    while p*p<=n:
        if n%p==0:
            yield p
            while n%p==0:n//=p
        p+=1
    if n>1:yield n
def labels(N,divs):
    assert all(N%p==0 for p in divs)
    divs=set(divs)
    g=1; D=s-2
    for p in divs:
        while D%p==0:D//=p;g*=p
    assert gcd(D,N)==1
    a,b=lucas2(N*g)
    assert a%g==0
    out=[3723%N,s%N,b%N,((a//g)*pow(D,-1,N))%N]
    _,A,B,C=out
    assert (B*B-A*(A-2)*B*C+(A-2)**2*C*C-1)%N==0
    return out
def crt(a,A,b,B):
    d=gcd(A,B)
    assert (a-b)%d==0
    q=B//d
    r=(a+A*((b-a)//d)*pow(A//d,-1,q))%lcm(A,B) if q>1 else a%A
    assert r%A==a%A and r%B==b%B
    return r,lcm(A,B)
def prime(p):return p>=2 and all(p%k for k in range(2,isqrt(p)+1))
tri=read('linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json',
         'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec')
assert tri['literal_scalar_J']==str(J)
assert int(tri['old_h_preserved_modulus'])==L
six=read('linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json',
         'd8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0')
XII=read('linked-detector-twelve-compatible-incidences-r1/EXACT-TWELVE-INCIDENCES.json',
         'b7db04b1bf6b1f606e29e5b7184f017dc0df3f970808c0e51bedaa3f0c5a5744')
assert int(XII['literal_scalar_J'])==J
P=[
(172237889,12767,3040,145589474,1163597,19),
(575921,736,185,14379,144073,23)]
old_h,old_step=int(XII['simultaneous_h_residue']),int(XII['simultaneous_h_modulus'])
assert old_step%L==0 and old_h%L==h0%L and old_step%2==old_h%2==0
low_odd_primes=[3,5,7,11,13,17]
assert all(old_step%p==0 and old_h%p!=1 for p in low_odd_primes)
new_h,new_step=old_h,old_step
old_r,old_rstep=int(XII['numeric_test_r']),int(XII['numeric_r_modulus'])
num,num_step=old_r,old_rstep
D=XII['numeric_test_d']; assert D==204
roots=[(-1,2),(-1,1),(1,2399),(-32,407)]
old_rows=tri['rows']+six['rows']+XII['rows']; assert len(old_rows)==12
assert len({r['prime']for r in old_rows}|{r[0]for r in P})==14

# Quotient through T0 for actual R; calculate exact denominator divisibility.
from fractions import Fraction
def K(x,y=0): return Fraction(x),Fraction(y)
def kadd(x,y): return x[0]+y[0],x[1]+y[1]
def ksc(x,c): return x[0]*c,x[1]*c
def ksub(x,y): return kadd(x,ksc(y,-1))
def km(x,y): return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def ks(x): return km(x,x)
def kd(x,y): return ksc(km(x,(y[0],-y[1])),1/(y[0]*y[0]-2*y[1]*y[1]))
Aquot=K(44,-24)
R=K(1,1),K(0,2)
d2=K(11,-6)
PX=ksub(R[0],kd(d2,R[0]))
PY=km(R[1],kadd(K(1),kd(d2,ks(R[0]))))
assert (PX,PY)==(K(24,-16),K(-160,116))
def on(P):return ks(P[1])==km(P[0],kadd(ks(P[0]),Aquot))
def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x,y=P; u,v=Q
    if x==u:
        if y==ksc(v,-1):return None
        assert y==v
        m=kd(kadd(ksc(ks(x),3),Aquot),ksc(y,2))
    else:m=kd(ksub(v,y),ksub(u,x))
    X=ksub(ks(m),kadd(x,u))
    ans=(X,ksub(km(m,ksub(x,X)),y))
    assert on(ans)
    return ans
def mul(n,P):
    Q=None
    while n:
        if n%2:Q=add(Q,P)
        P=add(P,P); n//=2
    return Q
assert on((PX,PY))

O=[]
for p,A,B,r,N,M in P:
    pp=p*p
    assert prime(p) and p>76176 and p==A*A+B*B and p%8==1
    W=mul(M,(PX,PY))
    denom=lcm(*(u.denominator for u in W[0]))
    ds=isqrt(denom);assert ds*ds==denom and ds%p==0 and ds%pp
    row=[]
    for rr,o in [(r,N),(p-r,M)]:
        r2=rr+p*(((2-rr*rr)//p)*pow(2*rr,-1,p)%p)
        assert r2*r2%pp==2
        _,point,U,formal=F(p,r2)
        fac=tuple(prime_factors(o))
        assert all(prime(q) for q in fac)
        assert formal(point(o)) and all(not formal(point(o//v)) for v in fac)
        os=point(o)
        assert os!=(0,0) and os[0]%p==os[1]==0
        NN=p*o
        ls=labels(NN,(*fac,p))
        us=[U(point(ell))[0]for ell in ls]
        assert all(w%p for w in us)
        f=prod(-pow(x,-1,pp)for x in us)%pp
        row.append({'root':rr,'root_p2':r2,'order':o,'order_prime_divisors':fac,
                    'formal_first_z':os,'label_period':NN,'literal_labels':ls,
                    'U_values':us,'product_fixedRoots':f})
    # Both full orders odd here, so opposite full order equals T0-quotient order.
    assert M%2==1 and prime(M)
    valA,valB=[z['product_fixedRoots']for z in row]
    norm=valA*valB%pp
    scales=[1,((valA+valB)*pow(2,-1,pp)+norm)%pp,norm]
    assert all(x%p for x in scales)
    theta=[a*pow(b,-1,pp)%pp for a,b in roots]
    xs=[v*pow(c*c,-1,p)%p for c in scales for v in theta]
    assert len(set(xs))==12 and 0 not in xs
    z=A*pow(B*r,-1,p)%p
    tgt=(theta[0]+p)%pp
    assert (z*z-tgt)%p==0
    z=(z+p*((tgt-z*z)//p)*pow(2*z,-1,p))%pp
    assert z*z%pp==tgt
    Ts=[pow(c*z,2,pp)for c in scales]
    contact=[prod((t-v)%pp for v in [0,*theta])%pp for t in Ts]
    assert Ts[0]==tgt and contact[0]%p==0 and contact[0] and all(t%p for t in contact[1:])
    num,num_step=crt(num,num_step,D*z,pp)
    new_h,new_step=crt(new_h,new_step,0,N)
    new_h,new_step=crt(new_h,new_step,1,M)
    new_h,new_step=crt(new_h,new_step,p**3,p**4)
    O.append({'prime':p,'AB':[A,B],'assigned_scale':0,'assigned_root_index':1,'arms':row,
              'quotient_x_denominator_sqrt':str(ds),'scales_mod_p2':scales,
              'distinct_nonzero_scaled_roots_mod_p':xs,'r_over_d_mod_p2':z,
              'T_j_mod_p2':Ts,'contact_values_mod_p2':contact})
assert new_step%old_step==0 and new_h%old_step==old_h
assert num_step%old_rstep==0 and num%old_rstep==old_r%old_rstep
for row in old_rows+O:
    p=row['prime']; e,f=[z['order']for z in row['arms']]
    assert new_h%(p**3*e)==0 and new_h%f==1 and new_h%p**4==p**3
    assert num*pow(D,-1,p*p)%(p*p)==row['r_over_d_mod_p2']
d_new=prod(z['prime']for z in O)
chars=[[q,pow(d_new,(q-1)//2,q)]for q in [3,5,7,11,13,17,19,23,29,31,37,41,43,47]]
assert d_new%8==1 and chars[:4]==[[3,1],[5,1],[7,1],[11,10]]
# From the older frozen p rows, fixed new class cofactor phases.
phases=[]
for R0 in old_rows:
    p=R0['prime']; a=R0['r_over_d_mod_p2']; assert a%p
    z=(a*a+pow(2,-1,p))%p; assert z
    m=pow(z*pow(d_new,-1,p)%p,(p-1)//2,p)
    assert m in (1,p-1)
    phases.append([p,1 if m==1 else -1])
real=run('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
         '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
real['Ball'].precision=32768
real['Ball'].S=1<<real['Ball'].precision
for step in range(40):
    H=new_h+new_step*step
    ok,Z=real['real_margin'](H)
    if ok:break
else:raise ArithmeticError('no passing real center in this control')
M=real['Ball'].S//(2**64)
iv=[Z.lo//M,-((-Z.hi)//M)]
assert 100*min(map(abs,iv))>2**64 and iv[0]*iv[1]>0
assert gcd(num,D)==1 and num*num>2*D*D
print(json.dumps({'literal_scalar_J':str(J),'prior_twelve_h_residue':str(old_h),
        'prior_twelve_h_modulus':str(old_step),'forbidden_low_odd_prime_divisors':low_odd_primes,
        'quotient_a':list(map(str,Aquot)),'quotient_point':[list(map(str,t))for t in (PX,PY)],
        'new_same_class_product':d_new,'new_product_euler_rows':chars,
        'new_class_remaining_cofactor_signs_at_old_contacts':phases,
        'rows':O,'simultaneous_h_residue':str(new_h),'simultaneous_h_modulus':str(new_step),
        'real_passing_step':step,'real_passing_h':str(H),'real_norm_interval_div_2pow64':iv,
        'numeric_test_d':D,'numeric_test_r':str(num),'numeric_r_modulus':str(num_step)},indent=2))
