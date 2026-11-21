#!/usr/bin/env python3
"""Add three original-ray partners while preserving the exact prior triad congruences."""
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
P=[
(52056721,1065,7136,11487837,1626706,13014713),
(53279089,3865,-6192,11697965,73988,2664341),
(95810641,-7671,-6080,80009662,4789765,1497281)]
h_tri,L_tri=int(tri['simultaneous_h_residue']),int(tri['simultaneous_h_modulus'])
assert L_tri%L==0 and h_tri%L==h0%L
new_h,new_step=h_tri,L_tri
num_tri, num_mod_tri=int(tri['numeric_test_r']),int(tri['numeric_r_modulus'])
num,num_step=num_tri,num_mod_tri
D=tri['numeric_test_d']; assert D==204
balance=(5,7,11,13,41)
witness_l=(23,19,19)
O=[]
for j,(p,A,B,r,N,M) in enumerate(P):
    pp=p*p
    assert prime(p) and p>76176 and p==A*A+B*B
    assert (A%16,B%16,A%7,B%7,p%408)==(9,0,1,3,1)
    q=tri['rows'][j]['prime']; assert tri['rows'][j]['assigned_scale']==j and p!=q
    assert [pow(p,(l-1)//2,l)for l in balance]==[pow(q,(l-1)//2,l)for l in balance]
    assert p%7==q%7==3
    ell=witness_l[j]
    assert pow(p*q,(ell-1)//2,ell)==ell-1
    row=[]
    for rr,o in [(r,N),(p-r,M)]:
        s2=rr+p*(((2-rr*rr)//p)*pow(2*rr,-1,p)%p)
        assert s2*s2%pp==2
        _,point,U,formal=F(p,s2)
        fac=tuple(prime_factors(o))
        assert all(prime(q) for q in fac)
        assert formal(point(o)) and all(not formal(point(o//v)) for v in fac)
        os=point(o)
        assert os!=(0,0) and os[0]%p==os[1]==0
        NN=p*o
        ls=labels(NN,(*fac,p))
        us=[U(point(ell))[0]for ell in ls]
        assert all(w%p for w in us)
        f=prod(-pow(x,-1,pp) for x in us)%pp
        row.append({'root':rr,'root_p2':s2,'order':o,'order_prime_divisors':fac,
                    'formal_first_z':os,'label_period':NN,'literal_labels':ls,
                    'U_values':us,'product_fixedRoots':f})
    a,b=[z['product_fixedRoots']for z in row]
    re=(a+b)*pow(2,-1,pp)%pp; norm=a*b%pp
    scales=[1,(re+norm)%pp,norm]; assert all(x%p for x in scales)
    theta=[-pow(2,-1,pp)%pp,pp-1,pow(2399,-1,pp),-32*pow(407,-1,pp)%pp]
    x=[v*pow(c*c,-1,p)%p for c in scales for v in theta]
    assert len(set(x))==12 and 0 not in x
    z=A*pow(B,-1,p)%p
    assert z*z%p==p-1
    z=(z+p*(((p-1-z*z)//p)*pow(2*z,-1,p)%p))%pp
    assert z*z%pp==p-1
    sratio=z*pow(scales[j],-1,pp)%pp
    Ts=[pow(c*sratio,2,pp) for c in scales]
    val=[prod((T-v)%pp for v in [0,*theta])%pp for T in Ts]
    assert Ts[j]==p-1 and Ts[j]%p!=1 and val[j]%p==0 and val[j]!=0
    assert all(val[k]%p for k in range(3) if k!=j)
    num,num_step=crt(num,num_step,D*sratio,pp)
    new_h,new_step=crt(new_h,new_step,0,N)
    new_h,new_step=crt(new_h,new_step,1,M)
    new_h,new_step=crt(new_h,new_step,p**3,p**4)
    O.append({'prime':p,'AB':(A,B),'assigned_scale':j,'prior_triad_prime':q,
              'pair_still_fails_saturation_character_at':ell, 'arms':row,'scales_mod_p2':scales,
              'distinct_nonzero_scaled_roots_mod_p':x,'r_over_d_mod_p2':sratio,
              'T_j_mod_p2':Ts,'contact_values_mod_p2':val})

for p,_,_,_,N,M in P:
    assert new_h%(p**3*N)==0 and new_h%M==1 and new_h%p**4==p**3
assert new_h%L_tri==h_tri%L_tri and new_step%L_tri==0
assert new_h%L==h0%L and new_h%5==h0%5==0
assert num%num_mod_tri==num_tri%num_mod_tri
for row in tri['rows']:
    p=row['prime']; a,b=[z['order'] for z in row['arms']]
    assert new_h%(p**3*a)==0 and new_h%b==1 and new_h%p**4==p**3
    assert num*pow(D,-1,p*p)%(p*p)==row['r_over_d_mod_p2']
real=run('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
         '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
real["Ball"].precision=16384
real["Ball"].S=1<<real["Ball"].precision
for j in range(40):
    H=new_h+new_step*j
    ok,Z=real['real_margin'](H)
    if ok:break
else:raise ArithmeticError("no passing real center in this control")
M=real['Ball'].S//(2**64)
iv=[Z.lo//M,-((-Z.hi)//M)]
assert 100*min(map(abs,iv))>2**64 and iv[0]*iv[1]>0
assert gcd(num,D)==1 and num*num>2*D*D
print(json.dumps({'literal_scalar_J':str(J),'old_h_preserved_modulus':str(L),
                  'prior_triad_h_residue':str(h_tri),'prior_triad_h_modulus':str(L_tri),
                  'five_balanced_character_primes':balance,
                  'rows':O,'simultaneous_h_residue':str(new_h),'simultaneous_h_modulus':str(new_step),
                  'real_passing_step':j,'real_passing_h':str(H),'real_norm_interval_div_2pow64':iv,
                  'numeric_test_d':D,'numeric_test_r':str(num),'numeric_r_modulus':str(num_step)},indent=2))
