"""Exact finite local orbit, labels and CRT for the actual scalar branch a=0."""
import math, json
R=4376874610839020
A=114444*R
B=204618888056724185
N=2**16
SUP=(2,3,5,11,17,163,661,733,1489,1861,13,37,53,131)
def vp(a,p):
    assert a
    e=0
    while a%p==0: e+=1; a//=p
    return e
class E:
    def __init__(self,p,d=None):
        self.p=p; self.d=d
        self.D=self.mul(self.Z(3)-self.S() if d is not None else (3,-1), self.Z(3)-self.S() if d is not None else (3,-1))
        self.Q=(self.Z(1)+self.S() if d is not None else (1,1), 2*self.S()%p if d is not None else (0,2))
        self.q=p if d is not None else p*p
    def Z(self,n):return n%self.p if self.d is not None else (n%self.p,0)
    def S(self):return self.d
    def addf(self,u,v):
        p=self.p
        return (u+v)%p if self.d is not None else ((u[0]+v[0])%p,(u[1]+v[1])%p)
    def negf(self,u):
        p=self.p
        return -u%p if self.d is not None else (-u[0]%p,-u[1]%p)
    def sub(self,u,v):return self.addf(u,self.negf(v))
    def mul(self,u,v):
        p=self.p
        if self.d is not None:return u*v%p
        a,b=u;c,d=v
        return ((a*c+2*b*d)%p,(a*d+b*c)%p)
    def inv(self,u):
        p=self.p
        if self.d is not None:return pow(u,-1,p)
        a,b=u; z=pow((a*a-2*b*b)%p,-1,p)
        return (a*z%p,-b*z%p)
    def add(self,Q,P):
        if Q is None:return P
        if P is None:return Q
        X,Y=Q;x,y=P
        if X==x and self.addf(Y,y)==self.Z(0):return None
        if X==x:
            assert Y==y
            m=self.mul(self.sub(self.mul(self.Z(3),self.mul(x,x)),self.D),self.inv(self.mul(self.Z(2),y)))
        else:
            m=self.mul(self.sub(Y,y),self.inv(self.sub(X,x)))
        z=self.sub(self.sub(self.mul(m,m),X),x)
        return z,self.sub(self.mul(m,self.sub(x,z)),y)
    def neg(self,Q):
        return None if Q is None else (Q[0],self.negf(Q[1]))
    def nsmul(self,n,Q=None):
        if Q is None:Q=self.Q
        if n<0:return self.neg(self.nsmul(-n,Q))
        T=None
        for bit in bin(n)[2:]:
            T=self.add(T,T)
            if bit=='1':T=self.add(T,Q)
        return T
    def order(self):
        q=self.q; d=math.isqrt(4*q)
        lo=q+1-d; h=math.isqrt(2*d+1)+1
        baby={}; T=None
        for i in range(h):
            baby.setdefault(T,i); T=self.add(T,self.Q)
        step=self.neg(T); target=self.neg(self.nsmul(lo))
        for j in range(2*d//h+2):
            if target in baby:
                n=lo+j*h+baby[target]
                assert self.nsmul(n) is None
                for p in factors(n):
                    while n%p==0 and self.nsmul(n//p) is None:n//=p
                assert self.nsmul(n) is None and all(self.nsmul(n//p) is not None for p in factors(n))
                return n
            target=self.add(target,step)
        raise ArithmeticError('Hasse interval order recovery')
    def recip(self,n):
        P=self.nsmul(n)
        if P is None:return self.Z(0)
        if P[0]==self.Z(0): raise ValueError('reciprocal pole')
        return self.inv(P[0])
def factors(n):
    p=2
    while p*p<=n:
        if n%p==0:
            yield p
            while n%p==0:n//=p
        p+=1
    if n>1:yield n
def places(p):
    s=[d for d in range(p) if (d*d-2)%p==0]
    return [E(p,d) for d in s] if s else [E(p)]

models={p:places(p) for p in SUP if p!=2}
orders={p:[e.order() for e in models[p]] for p in models}
h0=math.lcm(64,*(n for ns in orders.values() for n in ns))
# For each completion p odd, [h0]R is formal, so v(chartU) ≥1.
# At support p odd the only positive valuation of R is 1.
assert all(vp(R,p)<=1 for p in SUP if p!=2)
hc=math.lcm(h0,131) # v_131(order 44)=0, one extra factor suffices for v_131(U)≥2.
# Simultaneously v_p((n-1)/h0) ≥ ceil((15 v_p(R)+1)/2).
B0=6**15 * 3**N
need=hc*math.prod(p**((15*vp(R,p)+2)//2) for p in SUP)
J=need//math.gcd(B0,need)
shift=B0*J
assert shift%need==0
n=1+shift
step=math.prod(SUP)
# At support fields, shift≡0 mod each orbit order, so scalar label≡1,
# Lucas U_k,U_{k+1} reduce to -1,-1 (s=1, k≡4 mod6);
# z=U_k/(s-2) reduces to 1. Thus no expanded Lucas labels needed.
# For sign of guard, we use only its nonzero value modulo a certified
# (same) good prime. [h]R=O at all these residue fields, so one static check.
guards=[]
for ell in (3723,1,-1,1):
    witness=None
    for p,Es in models.items():
        try: vals=[e.recip(-2*ell) for e in Es]
        except ValueError: continue
        r=(sum(vals) * pow(2,-1,p))%p if len(Es)==2 else vals[0][0]
        if r:
            witness=(p,ell,r,vals)
            break
    assert witness
    guards.append(witness)
# Independent directed-rounding dyadic real interval computation.
class Ball:
    precision=4096
    S=1<<precision
    def __init__(self,x,y=None):
        self.lo=x if y is not None else x*self.S
        self.hi=y if y is not None else x*self.S
        assert self.lo<=self.hi
    def __add__(self,y):
        y=y if isinstance(y,Ball) else Ball(y)
        return Ball(self.lo+y.lo,self.hi+y.hi)
    __radd__=__add__
    def __neg__(self):return Ball(-self.hi,-self.lo)
    def __sub__(self,y):return self+-y
    def __rsub__(self,y):return -self+y
    def __mul__(self,y):
        y=y if isinstance(y,Ball) else Ball(y)
        s=self.S; v=[x*z for x in (self.lo,self.hi) for z in (y.lo,y.hi)]
        return Ball(min(v)//s,-((-max(v))//s))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=y if isinstance(y,Ball) else Ball(y)
        if -y.hi<=0<=-y.lo:raise ArithmeticError('need more precision')
        v=[(x*self.S,z) for x in (self.lo,self.hi) for z in (y.lo,y.hi)]
        return Ball(min(x//z for x,z in v),max(-((-x)//z) for x,z in v))
def real_u(n,s):
    S=Ball.S
    a=math.isqrt(2*S*S); e=s*Ball(a,a+1)
    D=(3-e)*(3-e)
    R=(1+e,2*e)
    def doub(P):
        x,y=P
        m=(3*x*x-D)/(2*y)
        T=m*m-2*x
        return T,m*(x-T)-y
    def add_to_R(Q):
        x,y=Q
        X,Y=R
        m=(y-Y)/(x-X)
        T=m*m-x-X
        return T,m*(x-T)-y
    P=R
    for b in bin(n)[3:]:
        P=doub(P)
        if b=='1':P=add_to_R(P)
    x,y=P
    return 2*y/(x*x+D)
def real_margin(n):
    a=real_u(n,1)*real_u(n,-1)
    lo=0 if a.lo<=0<=a.hi else min(abs(a.lo),abs(a.hi))
    hi=max(abs(a.lo),abs(a.hi))
    if 100*lo>Ball.S:return True,a
    assert 100*hi<Ball.S, 'boundary unresolved at this precision'
    return False,a
checked=[]
for j in range(1000):
    h=hc*(1+step*j)
    ok,v=real_margin(h)
    checked.append([j,h,v.lo,v.hi])
    if ok:break
else:raise ArithmeticError('increase search budget')
print(json.dumps({'orders':orders,'h0':hc,'step':step,'J':J,'n_label_bits':n.bit_length(),
                  'first_index':hc,'index_step':hc*step,'guard_residue_witnesses':guards,
                  'first_passing_h':h,'dyadic_interval_exponent':Ball.precision,
                  'real_margin_tests':checked},indent=2))
