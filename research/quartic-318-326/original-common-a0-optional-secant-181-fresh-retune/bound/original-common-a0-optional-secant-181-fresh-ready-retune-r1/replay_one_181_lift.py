from hashlib import sha256
from math import gcd, lcm
from pathlib import Path
import json

root=Path(__file__).resolve().parent.parent
base=root/'original-linear-q-a0-exact-anchor-depth-full-scalar-r1'

def pin(path,digest):
    raw=path.read_bytes()
    assert sha256(raw).hexdigest()==digest
    return json.loads(raw)

sh=pin(base/'EXACT-A0-FULL-SCALAR-ANCHOR-DEPTH.json','f06c9f02b2491e3b616aec205f48bdb1030f25054c78d03cae2230a940949ed1')
src=pin(base/'PINNED-ORDER-ONLY-Q.json','0f7167957a8e10351b0a0cba431ceed48557b84533c5fef7e25261b69f413254')
old=pin(root/'original-a0-factorless-companion-norm-line-r1'/'PINNED-SCALAR-FIBER.json','e26e3478e3980e48a762cde5eb9755f0e22c31db1b41e748f7b117ec15b2aefb')
p,T,R=181,909,4376874610839020
L0=p*T
h0,hs=old['h'],int(src['h'])
A_label=int(sh['A'])
i=(A_label*pow(3,32767,L0))%L0
j=(int(old['J'])*pow(6,15,T)*pow(3,65536,T))%T
assert h0==473592745039516333133760 and hs!=h0
assert (h0%T,i,j)==(378,123741,171)

def calc(mod):
    def z(a):return (a%mod,0)
    def plus(a,b):return ((a[0]+b[0])%mod,(a[1]+b[1])%mod)
    def minus(a,b):return ((a[0]-b[0])%mod,(a[1]-b[1])%mod)
    def mul(a,b):return ((a[0]*b[0]+2*a[1]*b[1])%mod,(a[0]*b[1]+a[1]*b[0])%mod)
    def norm(a):return (a[0]**2-2*a[1]**2)%mod
    def inv(a):
        d=pow(norm(a),-1,mod);return (a[0]*d%mod,-a[1]*d%mod)
    def div(a,b):return mul(a,inv(b))
    def square(a):return mul(a,a)
    d=square((3,-1));G=((1,1),(0,2))
    def add(U,V):
        if U is None:return V
        if V is None:return U
        x,y=U;X,Y=V
        if x==X:
            if plus(y,Y)==z(0):return None
            assert y==Y
            m=div(minus(mul(z(3),square(x)),d),mul(z(2),y))
        else:m=div(minus(Y,y),minus(X,x))
        u=minus(minus(square(m),x),X)
        return u,minus(mul(m,minus(x,u)),y)
    def step(h):
        a=None
        for bit in bin(h)[2:]:
            a=add(a,a)
            if bit=='1':a=add(a,G)
        return a
    def chart(h):
        x,y=step(h)
        return div(mul(z(2),y),plus(square(x),d))
    def packed(h,i):
        u,v=chart(h),chart(i)
        H,I=norm(u),norm(v); a=square(u)[0]
        N=(1+H**2*pow(R,-2,mod)+2*a*pow(R,-1,mod))%mod
        Q=I*pow(H*pow(R,15,mod),-1,mod)%mod
        return u,(H,a,N,Q,(N**2+R*Q**2)%mod,I)
    return step,packed

step,W=calc(p)
assert pow(2,90,p)==p-1
assert step(T) is None and all(step(T//q) is not None for q in [3,101])
r_old=W(378,j);r_new=W(378,i%T)
assert r_old==((65,44),(172,133,120,111,146,81))
assert r_new==((65,44),(172,133,120,29,144,119))
_,W2=calc(p*p); lifted=W2(8676,i)
assert lifted==((19336,7620),(21309,3419,6078,7201,0,26002))

beta=204618888056724185;t=18
A=1+3*beta*t*t;n=beta*(1-beta*t*t)*(1-9*beta*t*t);u=beta*A*A
point_y=8*beta**2*t*A*(1-3*beta*t*t)
a=point_y*pow(u,-1,p)%p; B0=12*n*n*pow(u,-1,p)%p
assert (A%p,a,B0)==(147,151,78)
d=1+114444*R
assert d%p==0 and d//p%p==132
assert (4*a*a+B0)%p==58 and pow(58,90,p)==p-1

rp=[2,3,5,11,17,163,661,733,1489,1861]
def val(n,p):
    v=0
    while n%p==0:n//=p;v+=1
    return v
orders=[o for row in sh['complete_odd_support_after_3'] for o in row['orders']]
assert len(orders)==10 and all(hs%o==0 for o in orders)
assert [val(hs,p) for p in [2,3,17]]==[6,5,1]
M=lcm(*orders,*[p**(val(hs,p)+1) for p in rp])
assert M==13315331113518436574832396171766859356800
assert gcd(M,L0)==9 and (hs+11422*M)%L0==8676
print(json.dumps(dict(scope='three named residue controls; no global square, index, or key', old=r_old,new_labels_on_old_h=r_new,
                      lifted=lifted, sharp_only_preservation_modulus=M,crt_period=lcm(M,L0),crt_seed_shift_in_M=11422,
                      old_half_point_order=T, secant_constants_mod_181=[A%p,a,B0]),indent=2,sort_keys=True))
