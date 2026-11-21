#!/usr/bin/env python3
"""Exact finite checks of the 4 canonical labels, guards and scale residues."""
import hashlib, json
from math import isqrt
from pathlib import Path
p=Path(__file__).resolve().parent.parent/'rc-linked-four-pole-common-q-r1'/'ACTUAL-COMMON-Q-SCALAR-PREFIX.json'
buf=p.read_bytes()
assert hashlib.sha256(buf).hexdigest()=="5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7"
a=json.loads(buf); h=int(a["h"]); i=6**15*3**65536*int(a["J"])
s=1+i; k=2*(s-2)
assert h>1 and h%64==0 and i%3**65536==0
assert s%2==1 and s%3==1 and k%6==4
assert 100*min(map(abs,a["norm_interval_div_2pow64"]))>2**64

def factors(n):
    for p in range(2,isqrt(n)+1):
        if n%p!=0:continue
        yield p
        while n%p==0:n//=p
    if n>1:yield n

def out(p,N):
    assert pow(2,(p-1)//2,p)==p-1 and not any(p%r==0 for r in range(2,isqrt(p)+1))
    assert h%N==i%N==0
    # Rigid explicit Lucas choice, not an observed Classical.choice.
    # M=[[s,-1],[1,0]] has order dividing 6 mod N, s=1 there.
    v=[0,1]
    for j in range(6):v.append((v[-1]-v[-2])%N)
    assert v[6:]==[0,1]
    ls=[3723%N,1,v[(k+1)%6],-v[k%6]%N]
    assert ls==[3723%N,1,N-1,1]
    zz=lambda n:(n%p,0)
    add=lambda x,y:((x[0]+y[0])%p,(x[1]+y[1])%p)
    sub=lambda x,y:((x[0]-y[0])%p,(x[1]-y[1])%p)
    def mul(x,y):
        a,b=x;c,d=y
        return (a*c+2*b*d)%p,(a*d+b*c)%p
    sq=lambda x:mul(x,x)
    norm=lambda x:(x[0]*x[0]-2*x[1]*x[1])%p
    inv=lambda x:mul((x[0],-x[1]),zz(pow(norm(x),-1,p)))
    div=lambda x,y:mul(x,inv(y))
    D=sq((3,-1)); R=((1,1),(0,2))
    def ec(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P; X,Y=Q
        if x==X and add(y,Y)==zz(0):return None
        if x==X:
            m=div(sub(mul(zz(3),sq(x)),D),mul(zz(2),y))
        else:m=div(sub(Y,y),sub(X,x))
        z=sub(sub(sq(m),x),X)
        return z,sub(mul(m,sub(x,z)),y)
    def mult(n):
        P=None
        for b in bin(n)[2:]:
            P=ec(P,P)
            if b=='1':P=ec(P,R)
            if P:
                x,y=P
                assert sq(y)==sub(mul(sq(x),x),mul(D,x))
        return P
    assert mult(N) is None and all(mult(N//r) is not None for r in factors(N))
    def u(n):
        if n%N==0:return zz(0)
        x,y=mult(n%N)
        return div(mul(zz(2),y),add(sq(x),D))
    gg=[sub(sq(u(n*(h-1)%N)),sq(u(n*h%N)))[0] for n in ls]
    rr=[div(zz(-1),u(n)) for n in ls]; prod=zz(1)
    for x in rr:prod=mul(prod,x)
    c1=(prod[0]+norm(prod))%p;c2=norm(prod)
    return dict(p=p,exact_order=N,explicit_label_residues=ls,
                rational_guard_mod_p=gg,fixedRoots_mod_p=rr,product=prod,scale_roots=[1,c1,c2])
r5=out(5,5)
assert r5["rational_guard_mod_p"]==a["guards_mod5"]==[4,1,1,1]
rq=out(a["q"],a["q_order"])
print(json.dumps(dict(h=str(h),scalar_label_bits=s.bit_length(),lucas_k_bits=k.bit_length(),
                      retain_exact_scalar_label=True,finite_residue_checks=[r5,rq]),indent=2))
