#!/usr/bin/env python3
"""Replay one actual selected-trace prime on a varying-h retained progression."""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import runpy,json
root=Path(__file__).resolve().parent.parent
def pinned(rel,hash256):
    f=root/rel
    assert sha256(f.read_bytes()).hexdigest()==hash256
    return f
src=pinned('linked-detector-w37-depth-r1/check_actual_shallow_formal.py',
           '4302feb27fa532f4e713e512a819c88c975a02993782f4ab9b346b590724ed63')
with redirect_stdout(StringIO()): field=runpy.run_path(str(src))['field']
data=json.loads(pinned('rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json',
                       '5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7').read_bytes())
def prime(p): return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def crt(a,A,b,B):
    d=gcd(A,B)
    assert (a-b)%d==0
    t=((b-a)//d)*pow(A//d,-1,B//d)%(B//d) if B//d>1 else 0
    N=lcm(A,B)
    x=(a+A*t)%N
    assert x%A==a%A and x%B==b%B
    return x,N
def lift_root(p,r,target):
    return (r+p*(((target-r*r)//p)*pow(2*r,-1,p)%p))%(p*p)
def verify_order(p,r,n,fs):
    r2=None if r is None else lift_root(p,r,2)
    if r2 is not None: assert r2*r2%(p*p)==2
    _,point,_,form=field(p,r2)
    assert prod(fs)==n and all(prime(q) for q in fs)
    assert form(point(n)) and all(not form(point(n//q)) for q in set(fs))
    return r2,point,form

h=int(data['h'])
oldL=int(data['h_CRT_step'])
assert oldL%64==0 and h%64==0
L=oldL
vp_old=[]
for q,n,fs in ((53,340,(2,2,5,17)),(131,44,(2,2,11)),(1041427,347142,(2,3,47,1231))):
    assert prime(q) and pow(2,(q-1)//2,q)==q-1 and h%q==0 and h%(q*q)!=0
    _,pt,ff=verify_order(q,None,n,fs)
    z=pt(h//q)
    assert ff(z) and z!=(0,0) and all(t%q==0 for t in z)
    assert pt(h)==(0,0)
    L=lcm(L,q**3*n)
    vp_old.append([q,n,z])
assert L%int(data['retained_scalar_modulus'])==0

p,A,B=3162001,1065,1424
assert prime(p) and p==A*A+B*B
assert (A%16,B%16,A%7,B%7,p%408)==(9,0,1,3,1)
arms=[]
for r,n,f in ((772448,791033,(29,27277)),(2389553,98746,(2,97,509))):
    assert r*r%p==2
    r2,pt,ff=verify_order(p,r,n,f)
    z=pt(n)
    assert ff(z) and z!=(0,0) and (z[0]%p,z[1])==(0,0)
    arms.append({'root':r,'root_mod_p2':r2,'order':n,'order_factors':f,'first_z_mod_p2':z})
assert sum(row['root'] for row in arms)==p
prim,alt=arms[1]['order'],arms[0]['order']
assert gcd(L,alt)==gcd(prim,alt)==gcd(p,L*prim*alt)==1 and gcd(L,prim)==2
# Exact old h residue + strong full-order formal entry + exact v_p(h)=3.
j,J=crt(h,L,0,prim)
j,J=crt(j,J,1,alt)
j,J=crt(j,J,p**3,p**4)
assert j>L and J%L==0 and J%64==0 and j%64==0

real_src=pinned('rc-linked-scalar-specialization-r1/select_scalar_specialization.py',
                '7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91')
with redirect_stdout(StringIO()): real=runpy.run_path(str(real_src))
for k in range(32):
    h_new=j+k*J
    passing,realball=real['real_margin'](h_new)
    if passing: break
else: raise ValueError("no certified guarded center")
q64=real['Ball'].S//2**64
I64=[realball.lo//q64, -((-realball.hi)//q64)]
assert I64[0]*I64[1]>0 and 100*min(map(abs,I64))>2**64
assert h_new%5==h%5==0 and data['guards_mod5']==[4,1,1,1]

# A genuine, explicit t local row: common depth at 2/3/17 can be
# increased by replacing D and repeating the same elementary CRT.
D=204
ss=(-A*pow(B,-1,p))%p
assert ss*ss%p==p-1
ss2=lift_root(p,ss,p-1)
assert ss2*ss2%(p*p)==p-1
Rnum,Rstride=crt(1,2*3*17,D*ss2,p*p)
assert gcd(Rnum,D)==1 and Rnum**2>2*D*D
u=Rnum**2; den=D**2
G=[u,2*u+den,u+den,2399*u-den,407*u+32*den]
assert [a%p for a in G if a%p==0]==[0] and G[2]%(p*p)!=0 and G[2]%p==0
assert (u-den)%p!=0
print(json.dumps({'p':p,'ray':[A,B],'arms':arms,'retained_old_scalar_depth_tests':vp_old,
                  'preserved_old_modulus':str(L),'new_h_residue':str(j),'new_h_modulus':str(J),
                  'real_passing_index':k,'real_passing_h':str(h_new),'real_norm_interval_div_2pow64':I64,
                  'test_contact_numroot':Rnum,'test_contact_denroot':D,'numroot_step':Rstride,
                  'contact_forms_mod_p2':[a%(p*p) for a in G]},indent=2))
