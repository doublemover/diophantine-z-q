from collections import defaultdict
import json
K=4;mod=2**K
def pol(x):return {i:t%mod for i,t in x.items() if t%mod}
def C(a):return pol({0:a})
def add(a,b):return pol({i:a.get(i,0)+b.get(i,0) for i in a.keys()|b.keys()})
def neg(a):return pol({i:-t for i,t in a.items()})
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 out=defaultdict(int)
 for i,x in a.items():
  for j,y in b.items():out[i+j]+=x*y
 return pol(out)
def sc(a,n):return pol({i:n*x for i,x in a.items()})
def sh(a,n):return {i+n:t for i,t in a.items()}
def iv(a):
 d,= [i for i,t in a.items() if t%2]
 q=sh(a,-d)
 b=sub(C(1),q)
 s=C(1);v=s
 for _ in range(1,K):
  v=mul(v,b);s=add(s,v)
 return sh(s,-d)
def pw(a,i):
 if i<0:return pw(iv(a),-i)
 out=C(1)
 while i:
  if i&1:out=mul(out,a)
  i//=2
  if i:a=mul(a,a)
 return out
def di(a,b):return mul(a,iv(b))
def cp(a,b):return sum_(sc(pw(b,i),t) for i,t in a.items())
def sum_(l):
 res={}
 for a in l:res=add(res,a)
 return res
s={1:1}; U=add(s,C(1));X=U
B=sub(pw(X,4),C(1));D2=di(pw(X,2),B)
catal=[1]
for n in range(1,K):catal.append(sum(catal[j]*catal[n-1-j] for j in range(n)))
# x/X² = x2pix avoids any temporary denominator at X=0.
x2pix=add(C(1),sum_(sc(di(pw(X,4*j-4),pw(B,2*j-1)),(-1)**(j-1)*4**j*catal[j-1]) for j in range(1,(K+1)//2)))
x=mul(pw(X,2),x2pix)
y=mul(mul(X,sub(pw(X,2),C(1))),x2pix)
y48=mul(pw(X,2),x)
x24=add(C(1),x)
y24=di(mul(X,add(add(y48,C(3)),sub(mul(pw(X,2),pw(x,2)),x))),sub(y48,C(1)))
t12=sub(di(y24,sub(x24,C(2))),C(3))
t6=di(pw(t12,2),add(t12,C(2)))
T=di(mul(pw(t6,2),add(t6,C(9))),pw(add(t6,C(8)),2))
E=sub(T,X);assert all(v%2==0 for v in E.values())
Y=U
for i in range(K):Y=sub(U,cp(E,sub(Y,C(1))))
assert cp(T,sub(Y,C(1)))==U
a=add(pw(x,2),C(3));b=sub(sub(sc(pw(x,2),3),sc(x,4)),C(3))
W=di(mul(y,pw(a,2)),add(sub(sc(pw(y,4),8),sc(mul(mul(b,x),pw(y,2)),4)),mul(b,pw(a,2))))
ss=[1];bb=[0]
for n in range(1,K//2+1):
 ss.append(-2*ss[n-1]-3*sum(ss[i]*ss[n-2-i] for i in range(n-1)))
 bb.append(n*ss[n]-sum(bb[i]*ss[n-i] for i in range(1,n)))
L=add(W,sum_(sc(pw(W,2*j+1),pow(2,2*j,mod)*bb[j]*pow(2*j+1,-1,mod)) for j in range(1,K//2+1)))
L=cp(L,sub(Y,C(1)))
assert not [a0 for a0 in L if a0>=0]
# Model the exact canonical tame quotient J₂ from the two branches of t₆.
Q=di(mul(pw(s,2),add(s,C(9))),pw(add(s,C(8)),2))
Q=sub(Q,s) # Q(X)≡constant1
v=s
for i in range(K):v=sub(U,cp(Q,v))
Ju=di(mul(v,pw(add(v,C(9)),2)),add(v,C(8)))
assert all(t%2==0 for t in sub(Ju,pw(U,2)).values())
JF=sub(Ju,C(1))

P0=pol({-1:1,-2:4,-5:8,-3:8})
phase0=pol({-9:8,-3:8})
assert L==add(sub(cp(P0,JF),P0),phase0)
assert cp(add(Q,s),v)==U
assert all(x%8==0 for x in sub(Ju,pw(U,2)).values())

# Independent F_32 model for the actual norm36 D119 residue canary.
def fmul(x,y):
    acc=0
    for b in range(5):
        if y>>b&1:acc^=x<<b
    for b in range(8,4,-1):
        if acc>>b&1:acc^=0b100101<<(b-5)
    return acc
def fpow(a,n):
    s=1
    while n:
        if n&1:s=fmul(s,a)
        n//=2
        if n:a=fmul(a,a)
    return s
assert fpow(2,31)==1 and all(fpow(2,i)!=1 for i in range(1,31))
def tr(a):
    s=0
    for _ in range(5):
        s^=a;a=fmul(a,a)
    assert s in (0,1)
    return s
js=lambda u:u^fpow(u,28)
jt=lambda u:fpow(u,3)^fpow(u,30)
orbit={}
for a in range(2,32):
    v0=fpow(a,4)
    for b in range(2,32):
        if b!=fpow(a,30) and v0!=fpow(b,30) and jt(a)==js(b) and jt(b)==js(v0):
            assert a not in orbit
            orbit[a]=b
assert len(orbit)==10
r0=min(orbit); r1=orbit[r0]
half=lambda r:{fpow(r,2**i) for i in range(5)}
p0,p1=half(r0),half(r1)
assert p0|p1==set(orbit) and not p0&p1
data=[]
for part in (p0,p1):
    s0=s1=s2=s3=0
    for u in sorted(part):
        z=fpow(u^1,30)
        q=fpow(z,9)^fpow(z,3)
        v=fpow(z,2)^z
        edge=fpow(js(u),30)^fpow(jt(u),30)
        assert edge==v
        cob=fpow(z,5)^fpow(z,3)
        assert q^fpow(v,5)==(fpow(cob,2)^cob)
        s0^=q;s1^=fpow(v,5)
        s2^=fpow(js(u),30)
        s3^=fpow(u,1)
    assert s0==s1 and s0 in (0,1) and s2 in (0,1)
    data.append(dict(labels=sorted(part),log_over_8_mod2=s0,source_igusa_8_bit=s2))
assert sorted(x['log_over_8_mod2'] for x in data)==[0,1]
assert len({x['source_igusa_8_bit'] for x in data})==1
def arr(a):return [[i,t] for i,t in sorted(a.items())]
print(json.dumps(dict(scope="actual production sufficient phase, evaluated only on the genuine D119 reference",
  exact_modulus=mod, tame_log_L=arr(L), canonical_tame_Frobenius_u=arr(Ju),
  coboundary_primitive=arr(P0), logarithmic_residual=arr(phase0),
  D119_GH_halves=data),indent=2,sort_keys=True))
