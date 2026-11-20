"""Exact compact numerator and L support conditions, at accessible primes."""
import contextlib,io,math,json,sys
from pathlib import Path
base=Path(__file__).resolve().parent.parent/'rc-linked-scalar-specialization-r1'
sys.path.insert(0,str(base))
with contextlib.redirect_stdout(io.StringIO()):
    import check_actual_scalar_modular as F
C=F.C

def sqrt2(p):
    if pow(2,(p-1)//2,p)!=1:return None
    n,s=p-1,0
    while n%2==0:n//=2;s+=1
    if s==1:return pow(2,(p+1)//4,p)
    z=2
    while pow(z,(p-1)//2,p)!=p-1:z+=1
    x=pow(2,(n+1)//2,p);b=pow(2,n,p);g=pow(z,n,p)
    while b!=1:
        j=1;h=b*b%p
        while h!=1:h=h*h%p;j+=1
        assert j<s
        t=pow(g,2**(s-j-1),p)
        x=x*t%p;g=t*t%p;b=b*g%p;s=j
    assert x*x%p==2
    return x

def fast_places(p):
    x=sqrt2(p)
    return [C.E(p)] if x is None else [C.E(p,z) for z in sorted([x,p-x])]
C.places=fast_places

def primes(hi):
    flag=bytearray(b'\x01')*(hi+1)
    flag[:2]=b'\x00\x00'
    for p in range(2,math.isqrt(hi)+1):
        if flag[p]:flag[p*p::p]=b'\x00'*(1+(hi-p*p)//p)
    return (p for p,f in enumerate(flag) if f)

def symbol(x,p):
    n=pow(x%p,(p-1)//2,p)
    return -1 if n==p-1 else n
bound=int(sys.argv[1]) if len(sys.argv)>1 else 120000
rows=[];excluded=passed=0
for p in primes(bound):
    if p<11 or C.R*(C.A+1)*17%p==0:continue
    if symbol(C.B,p)!=1:continue
    try:
        if p in C.SUP:
            b=C.A*pow(1+C.A,-1,p)**2%p
            r={'prime':p,'delta':(1-b*pow(17,-1,p))%p,'W':1}
        else:r=F.residue(p)
    except ValueError:
        excluded+=1;continue
    passed+=1
    c=12*r['W']*pow(1+C.A,-1,p)%p
    d=C.B*c*c%p
    assert d==(1-r['delta'])%p
    branch='C' if c==0 else 'L' if (25*d-9)%p==0 else None
    if branch:
        r.update(branch=branch,c_mod_p=c,D_mod_p=d,split_norm_partner=symbol(-C.R,p))
        rows.append(r)
# Refine the inert chart in the degree-two unramified integer basis.
def refine_inert(p,i,order,prec=128):
    i%=p*order
    if i==0:return (0,0)
    class V:
        def __init__(self,r,ex=0,N=prec):
            rr,ii=r if isinstance(r,tuple) else (r,0)
            assert N>=ex
            q=p**(N-ex);rr%=q;ii%=q
            if rr or ii:
                while rr%p==ii%p==0:
                    rr//=p;ii//=p;ex+=1
            else:ex=N
            self.r,self.j,self.ex,self.N=rr,ii,ex,N
        @classmethod
        def typ(cls,r):return r if isinstance(r,V) else V(r)
        def __add__(self,w):
            w=V.typ(w);v=min(self.ex,w.ex);N=min(self.N,w.N)
            k=p**(self.ex-v);l=p**(w.ex-v)
            return V((k*self.r+l*w.r,k*self.j+l*w.j),v,N)
        __radd__=__add__
        def __neg__(self):return V((-self.r,-self.j),self.ex,self.N)
        def __sub__(self,w):return self+-V.typ(w)
        def __rsub__(self,w):return V.typ(w)+-self
        def __mul__(self,w):
            w=V.typ(w)
            return V((self.r*w.r+2*self.j*w.j,self.r*w.j+self.j*w.r),
                self.ex+w.ex,min(self.N+w.ex,w.N+self.ex))
        __rmul__=__mul__
        def __truediv__(self,w):
            w=V.typ(w);d=w.N-w.ex
            assert d>0, 'cannot invert an unresolved local ball'
            u=pow(w.r*w.r-2*w.j*w.j,-1,p**d)
            return self*V((u*w.r,-u*w.j),-w.ex,d-w.ex)
        def res(self):
            assert self.N>=2 and self.ex>=0
            t=p**self.ex
            return self.r*t%(p*p),self.j*t%(p*p)
    e=V((0,1));D=(3-e)*(3-e);R=(1+e,2*e)
    T=R
    for bit in bin(i)[3:]:
        x,y=T;m=(3*x*x-D)/(2*y);X=m*m-2*x
        T=X,m*(x-X)-y
        if bit=='1':
            x,y=T;X,Y=R;m=(y-Y)/(x-X);X0=m*m-x-X
            T=X0,m*(x-X0)-y
    x,y=T
    return (2*y/(x*x+D)).res()

for row in rows:
    p=row['prime'];Es=C.places(p);O=row['orders'];m=p*p
    if len(Es)==2:
        chart=[[F.refine_split(p,i,n,e.d) for e,n in zip(Es,O)] for i in (C.h,C.shift)]
        u,v=chart
        H=u[0]*u[1]%m
        f=(u[0]**2+u[1]**2)*pow(2,-1,m)%m
        I=v[0]*v[1]%m
    else:
        chart=[refine_inert(p,i,O[0]) for i in (C.h,C.shift)]
        u,v=chart
        H=(u[0]**2-2*u[1]**2)%m
        f=(u[0]**2+2*u[1]**2)%m
        I=(v[0]**2-2*v[1]**2)%m
    Q=I*pow(H*pow(C.R,15,m)%m,-1,m)%m
    N=(1+(H*pow(C.R,-1,m)%m)**2+2*f*pow(C.R,-1,m))%m
    W=(N*N+C.R*Q*Q)%m
    c=12*W*pow(1+C.A,-1,m)%m
    D=C.B*c*c%m;fL=(25*D-9)%m
    assert (c if row['branch']=='C' else fL)%p==0
    efield='c' if row['branch']=='C' else '25D_minus_9'
    val=c if row['branch']=='C' else fL
    row['mod_p_squared']={'reduced_indices':[[i%(p*n) for n in O] for i in (C.h,C.shift)],
        'charts':chart,'H':H,'I':I,'W':W,'c':c,'D':D,'25D_minus_9':fL,
        'order_if_simple':{efield:1 if val else None},'unit_mod_p':val//p}
# p=7 is bad at one split place. Verify first returns directly on the
# smooth locus (the singular reduction is the cusp y²=x³).
p=7; Es=C.places(p)
def first_return(e):
    T=e.Q
    for b in range(1,30):
        if T is None:return b
        if e.D==0: assert T!=(0,0)
        T=e.add(T,e.Q)
    raise ArithmeticError('first return')
oo=[first_return(e) for e in Es]
assert oo==[7,4]
uu,ii=[[F.refine_split(p,i,o,e.d) for e,o in zip(Es,oo)] for i in (C.h,C.shift)]
HH=uu[0]*uu[1]%(p*p); II=ii[0]*ii[1]%(p*p)
assert HH%p==II%p==0 and HH and II
ff=(uu[0]**2+uu[1]**2)*pow(2,-1,p)%p
QQ=(II//p)*pow((HH//p)*pow(C.R,15,p),-1,p)%p
NN=(1+2*ff*pow(C.R,-1,p))%p
WW=(NN*NN+C.R*QQ*QQ)%p
cc=12*WW*pow(1+C.A,-1,p)%p
DD=C.B*cc*cc%p
assert cc and (25*DD-9)%p and (1-DD)%p
bad7={'orders':oo,'charts_mod_49':[uu,ii],'norms_mod_49':[HH,II],
      'W_mod_7':WW,'c_mod_7':cc,'D_mod_7':DD}

from itertools import product
B=(5,11,17,163,661,733,1489,1861)
S=(-1,2)+B
def loc(n,p):
    e=0
    while n%p==0:e+=1;n//=p
    return e%2,symbol(n,p)
groups={}
for factors in product((0,1), repeat=len(rows)):
    f=math.prod(row['prime']**e for e,row in zip(factors,rows))
    candidates=[]
    for bits in product((0,1),repeat=len(S)):
        x=f*math.prod(z**e for z,e in zip(S,bits))
        if not all(loc(x,p) in (loc(-1,p),loc(C.B,p)) for p in B):continue
        if not all(loc(x,p)==loc(-2,p) for p in (131,6551)):continue
        candidates.append(x)
    groups[f]=sorted(candidates)
print(json.dumps({'bound':bound,'accessible_tested':passed,'inaccessible':excluded,
    'xi_support_primes':rows,'bad_seven_good_auxiliary_reduction':bad7,
    'known_support_beta_and_two_H_prime_survivors':groups},indent=2))
