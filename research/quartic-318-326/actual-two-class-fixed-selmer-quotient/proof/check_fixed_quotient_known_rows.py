#!/usr/bin/env python3
"""Check fixed scale small places plus exact bounded known-support Selmer quotient."""
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

# Exact local ratio c_1/c_2 = 1 + Re(product of four U charts).
from functools import reduce
from itertools import product
small=[]
for p in (3,5,11,17,37,2399):
    pp=p*p
    guesses=[r for r in range(p) if r*r%p==2] or [None]
    rr=[]
    for r in guesses:
        r2=None if r is None else r+p*(((2-r*r)//p)*pow(2*r,-1,p)%p)
        ord_,point,U,formal=F(p,r2)
        o=ord_()
        fac=tuple(prime_factors(o))
        assert formal(point(o)) and all(not formal(point(o//q))for q in fac)
        ls=labels(p*o,(*fac,p))
        us=[U(point(n))for n in ls]
        def mul(x,y):
            a,b=x;c,d=y
            return ((a*c+2*b*d)%pp,(a*d+b*c)%pp)
        tot=reduce(mul,us,(1,0))
        rr.append({'root':r,'point_order':o,'literal_labels_mod_period':ls,'U_charts_p2':us,'product_U':tot})
    re=rr[0]['product_U'][0] if len(rr)==1 else sum(z['product_U'][0]for z in rr)*pow(2,-1,pp)
    eta=(1+re)%pp
    small.append({'p':p,'ratio_mod_p2':eta,'arms':rr})
assert [z['ratio_mod_p2']for z in small]==[6,10,48,209,1269,1073341]
s=-32*407*2399**2
assert s//32%8==1 and 2399%8==7
assert (s+640)//32%8==5 and (640//128)%8==5

def oddc(x,p):
    k=0
    while x%p==0:x//=p;k+=1
    r=pow(x%p,(p-1)//2,p); assert r in (1,p-1)
    return k%2,0 if r==1 else 1
def eq2(x):
    e=0
    while not x%2:e^=1;x//=2
    return (e,x%8)
def Tlocal(p,eta):
    t=2399*407**2*eta**2
    E=[0,s,t]
    L=[((0,0),)*3]
    for i in range(3):
        dd=[E[i]-E[j]for j in range(3)]
        dd[i]=prod(dd[j]for j in range(3)if j!=i)
        L.append(tuple(oddc(x,p)for x in dd))
    assert len({tuple(e for e,v in r)for r in L})==4
    return L
loc={z['p']:Tlocal(z['p'],z['ratio_mod_p2'])for z in small if z['p']in (11,37,2399)}
assert all(z['ratio_mod_p2']%z['p']!=0 for z in small if z['p']in (11,37,2399))
assert small[0]['ratio_mod_p2']%3==small[1]['ratio_mod_p2']%5==0
assert small[0]['ratio_mod_p2'] and small[1]['ratio_mod_p2']
assert 814%3==1 and pow(814,2,5)==1
u=small[3]['ratio_mod_p2']
assert u%17 and (407*u*u+32*2399)%17
PA,PB=415721,9807649
assert PA%8==PB%8==1 and pow(PA,(PB-1)//2,PB)==pow(PB,(PA-1)//2,PA)==1
pr=[-1,2,3,5,11,37,2399]
surv={}
for A,B in product(range(1<<len(pr)),repeat=2):
    x=[prod(pr[i]for i in range(len(pr))if m>>i&1)for m in [A,B,A^B]]
    if x[1]<0 or any(pow(u%PA,(PA-1)//2,PA)!=1 for u in x) or pow(x[2]%PB,(PB-1)//2,PB)!=1:continue
    for e,f,g in product(range(2),repeat=3):
        u=(e,f,e^f); v=(g,g,0)
        d=[x[i]*PA**u[i]*PB**v[i] for i in range(3)]
        if eq2(d[2])!=(0,1) or any(oddc(d[1],p)!=(0,0)for p in (3,5)):continue
        if any(tuple(oddc(y,p)for y in d)not in rs for p,rs in loc.items()):continue
        mask=A+(B<<7)+(e<<14)+(f<<15)+(g<<16)
        surv[mask]={'static':x,'collapsed_a':u,'collapsed_b':v}
assert len(surv)==16
basis_specs=[
    {'static':[1,1,1],'collapsed_a':(1,0,1),'collapsed_b':(0,0,0)},
    {'static':[131945,1,131945],'collapsed_a':(0,0,0),'collapsed_b':(0,0,0)},
    {'static':[-1952786,814,-2399],'collapsed_a':(0,0,0),'collapsed_b':(0,0,0)},
    {'static':[2399,2399,1],'collapsed_a':(0,1,1),'collapsed_b':(1,1,0)}]
masks=[next(k for k,v in surv.items()if v==q)for q in basis_specs]
sp={0}
for m in masks:sp|={t^m for t in sp}
assert sp==set(surv)
print(json.dumps({'anchor_ratio_rows':small,'three_additive_odd_Kummer_images':loc,
                  'known_static_support':pr[1:],'known_finite_slice_dimension':4,
                  'basis_of_known_tests_not_full_quotient':basis_specs,
                  'surviving_rows':[surv[m]for m in sorted(surv)]},indent=2))
