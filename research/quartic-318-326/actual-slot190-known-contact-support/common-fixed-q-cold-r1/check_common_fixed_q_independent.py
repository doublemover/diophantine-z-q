import json,sys,math
from pathlib import Path
p=1041427
d=json.loads(Path(sys.argv[1]).read_text())
h=int(d['h']); beta=204618888056724185; R=4376874610839020; M=1+2448*beta
assert beta*4==R*11*17 and math.gcd(p,42*R*M*beta)==1 and all(p%r for r in range(2,math.isqrt(p)+1))
assert pow(2,(p-1)//2,p)==p-1
# A separate exact Jacobian computation needs no inversion through reduction to zero.
mod=p**4
class Q:
    def __init__(self,a,b=0): self.a=a%mod; self.b=b%mod
    def __add__(self,o):
        if not isinstance(o,Q): o=Q(o)
        return Q(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self): return Q(-self.a,-self.b)
    def __sub__(self,o): return self+-o
    def __rsub__(self,o): return o+-self
    def __mul__(self,o):
        if not isinstance(o,Q): o=Q(o)
        return Q(self.a*o.a+2*self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def __pow__(self,n):
        assert n>=0
        acc=Q(1); b=self
        while n:
            if n%2:acc=acc*b
            b=b*b;n//=2
        return acc
    def __eq__(self,o):
        if not isinstance(o,Q):o=Q(o)
        return (self.a,self.b)==(o.a,o.b)
    def norm(self): return (self.a**2-2*self.b**2)%mod
    def inv(self): return Q(self.a,-self.b)*pow(self.norm(),-1,mod)
    def __truediv__(self,o): return self*(o if isinstance(o,Q) else Q(o)).inv()
    def __repr__(self): return str((self.a,self.b))
u=Q(0,1); a=-(3-u)**2; G=(1+u,2*u,Q(1))
def dbl(T):
    X,Y,Z=T
    M=3*X**2+a*Z**4; W=4*X*Y**2; T0=M**2-2*W
    return T0,M*(W-T0)-8*Y**4,2*Y*Z
def plus_g(T):
    X,Y,Z=T
    X0,Y0,_=G
    H=X0*Z**2-X; K=Y0*Z**3-Y; V=H**2*X
    X1=K**2-H**3-2*V
    return X1,K*(V-X1)-H**3*Y,Z*H
def point(n):
    T=G
    for bit in bin(n)[3:]:
        T=dbl(T)
        if bit=='1':T=plus_g(T)
        X,Y,Z=T
        assert X.a%p or X.b%p or Y.a%p or Y.b%p or Z.a%p or Z.b%p
        assert Y**2==X**3+a*X*Z**4
    return T
n=d['q_order']
assert n==347142
fac=[]
v=n
for l in range(2,math.isqrt(n)+1):
    if v%l==0:
        fac.append(l)
        while v%l==0: v//=l
if v>1:fac.append(v)
assert all(point(n//l)[2].norm()%p for l in fac)
X,Y,Z=point(n);z=-(X*Z)/Y
assert z.a%p==z.b%p==0 and (z.a%(p*p) or z.b%(p*p))
assert -2*z==2*Y*Z/(X**2-a*Z**4)
def form_U(k):
    t,e=divmod(k,n); assert e==0
    return -2*t*z
K=6**15*3**65536; i=K*int(d['J'])
assert i%h==0 and (i//h)%(p*p)==7
Uh,Ui=form_U(h),form_U(i)
assert not(Uh.a%p**2 or Uh.b%p**2) and (Uh.a%p**3 or Uh.b%p**3)
assert not(Ui.a%p**2 or Ui.b%p**2)
rat=Q(Ui.a//p**2, Ui.b//p**2)/Q(Uh.a//p**2,Uh.b//p**2)
assert rat.a%(p*p)==7 and rat.b%(p*p)==0
N=(1+Uh**2/R).norm()
Qpack=rat.norm()*pow(R,-15,mod)%mod
W=(N*N+R*Qpack*Qpack)%mod
c=12*W*pow(M,-1,mod)%mod
delta=(1-beta*c*c)%mod
Arad=(1-21060**2*delta)%mod
assert [u%(p*p) for u in (W,c,delta,Arad)]==d['q2_W_c_delta_K_radicand']
assert delta%p==880334 and Arad%p==376271
assert pow(delta,(p-1)//2,p)==p-1 and pow(Arad,(p-1)//2,p)==1
print('ordinary affine origin guard, exact return',n,'proper-order factors',fac,'new q²',[u%(p*p) for u in (W,c,delta,Arad)])
# Fixed-point interval arithmetic with 3072 fractional bits, independent doubling x identity.
S=1<<3072
class I:
    def __init__(self,l,r=None): self.l,self.r=(l*S,l*S) if r is None else (l,r)
    def __neg__(self): return I(-self.r,-self.l)
    def __add__(self,o):
        if isinstance(o,int):o=I(o)
        return I(self.l+o.l,self.r+o.r)
    __radd__=__add__
    def __sub__(self,o): return self+-o
    def __rsub__(self,o): return o+-self
    def __mul__(self,o):
        if isinstance(o,int):o=I(o)
        a=tuple(x*y for x in (self.l,self.r) for y in (o.l,o.r))
        return I(min(a)//S,-(-max(a)//S))
    __rmul__=__mul__
    def __truediv__(self,o):
        assert self.l<=self.r and (o.l>0 or o.r<0)
        a=tuple((x*S,y) for x in (self.l,self.r) for y in (o.l,o.r))
        return I(min(v//w for v,w in a),max(-(-v//w) for v,w in a))
    def __pow__(self,n):
        assert n>=0
        o=I(1)
        for _ in range(n):o=o*self
        return o
sq=math.isqrt(2*S*S)
def real_U(root):
    x0=1+root;y0=2*root;E=(3-root)**2
    x,y=x0,y0
    for bit in bin(h)[3:]:
        lam=(3*x*x-E)/(2*y)
        xx=(x*x+E)**2/(4*y*y)
        x,y=xx,lam*(x-xx)-y
        if bit=='1':
            lam=(y-y0)/(x-x0); xx=lam**2-x-x0
            x,y=xx,lam*(x-xx)-y
    return 2*y/(x*x+E)
interval=real_U(I(sq,sq+1))*real_U(-I(sq,sq+1))
q=1<<(3072-64)
lo=interval.l//q;hi=-(-interval.r//q)
assert (lo,hi)==tuple(d['norm_interval_div_2pow64'])
assert 0<lo<hi and 100*lo>2**64
print('independent outward real norm:',(lo,hi),'/ 2^64')
