"""Local theta from the literal compressed a=0 specialization, never W=1."""
import contextlib,io,json,math,sys
with contextlib.redirect_stdout(io.StringIO()):
    import select_scalar_specialization as C

def parent_poly(p,vals):
    return vals[0]*vals[1]%p if len(vals)==2 else (vals[0][0]**2-2*vals[0][1]**2)%p

def chartmod(e,i):
    P=e.nsmul(i)
    if P is None:return e.Z(0)
    x,y=P
    den=e.addf(e.mul(x,x),e.D)
    if den==e.Z(0):raise ValueError('pole')
    return e.mul(e.mul(e.Z(2),y),e.inv(den))

def residue(p):
    es=C.places(p)
    os=[e.order() for e in es]
    u=[chartmod(e,C.h%o) for e,o in zip(es,os)]
    v=[chartmod(e,C.shift%o) for e,o in zip(es,os)]
    hh=parent_poly(p,u)
    if not hh:raise ValueError('H nonunit')
    f=(u[0]**2+u[1]**2)*pow(2,-1,p)%p if len(u)==2 else (u[0][0]**2+2*u[0][1]**2)%p
    i=parent_poly(p,v)
    q=i*pow(hh*pow(C.R,15,p)%p,-1,p)%p
    z=(1+(hh*pow(C.R,-1,p)%p)**2+2*f*pow(C.R,-1,p))%p
    w=(z*z+C.R*q*q)%p
    b=C.A*(w*pow(1+C.A,-1,p))**2%p
    return dict(prime=p,orders=os,H=hh,I=i,W=w,b=b,delta=(1-b*pow(17,-1,p))%p)

def isprime(p):return p>=2 and all(p%j for j in range(2,math.isqrt(p)+1))
rows=[]
for p in range(5,10000):
    if not isprime(p) or C.R*(C.A+1)*119 % p==0 or p in C.SUP:continue
    try: r=residue(p)
    except ValueError:continue
    if r['delta']==0:
        rows.append(r)

# Higher precision at a split prime; integer modular balls and precision
# propagation only. (u,v,N) denotes p^v*u + p^N Z_p, with u reduced/unit.
def square_root_mod(p,d,N):
    q=p
    for j in range(1,N):
        d += (-((d*d-2)//q)*pow(2*d,-1,p)%p)*q
        q*=p
        assert (d*d-2)%q==0
    return d
def refine_split(p,n,prime_order,root,P=128):
    mod=p**2
    n%=p*prime_order
    if n==0:return 0 # formal parameter is in p²: kernel p·ord of reduction
    class V:
        def __init__(self,u,v=0,N=P):
            assert N>=v
            u%=p**(N-v)
            if u:
                while u%p==0:u//=p;v+=1
            else:v=N
            self.u,self.v,self.N=u,v,N
        @classmethod
        def typ(cls,x):return x if isinstance(x,V) else V(x)
        def __add__(self,y):
            y=V.typ(y);v=min(self.v,y.v);N=min(self.N,y.N)
            return V(self.u*p**(self.v-v)+y.u*p**(y.v-v),v,N)
        __radd__=__add__
        def __neg__(self):return V(-self.u,self.v,self.N)
        def __sub__(self,y):return self+-V.typ(y)
        def __rsub__(self,y):return V.typ(y)+-self
        def __mul__(self,y):
            y=V.typ(y)
            return V(self.u*y.u,self.v+y.v,min(self.N+y.v,y.N+self.v))
        __rmul__=__mul__
        def __truediv__(self,y):
            y=V.typ(y)
            assert y.u, 'insufficient precision for inverse'
            rel=y.N-y.v
            return self*V(pow(y.u,-1,p**rel),-y.v,rel-y.v)
        def res(self):
            assert self.N>=2 and self.v>=0
            return self.u*p**self.v%mod
    e=V(square_root_mod(p,root,P))
    D=(3-e)*(3-e)
    R=(1+e,2*e)
    def db(P):
        x,y=P;m=(3*x*x-D)/(2*y)
        X=m*m-2*x
        return X,m*(x-X)-y
    def add_R(P):
        x,y=P;X,Y=R;m=(y-Y)/(x-X)
        X0=m*m-x-X
        return X0,m*(x-X0)-y
    T=R
    for bit in bin(n)[3:]:
        T=db(T)
        if bit=='1':T=add_R(T)
    x,y=T
    return (2*y/(x*x+D)).res()

for row in rows:
    p=row['prime']; Es=C.places(p); O=row['orders'];m=p*p
    if len(Es)!=2:continue
    charts=[[refine_split(p,idx,o,e.d) for o,e in zip(O,Es)] for idx in (C.h,C.shift)]
    u,v=charts
    hh=u[0]*u[1]%m
    f=(u[0]**2+u[1]**2)*pow(2,-1,m)%m
    i=v[0]*v[1]%m
    q=i*pow(hh*pow(C.R,15,m)%m,-1,m)%m
    z=(1+(hh*pow(C.R,-1,m)%m)**2+2*f*pow(C.R,-1,m))%m
    w=(z*z+C.R*q*q)%m
    b=C.A*(w*pow(1+C.A,-1,m))**2%m
    de=(1-b*pow(17,-1,m))%m
    assert not de%p and de%m
    unit=de//p
    row['precision_two']={'chart_coefficients':charts,'h_shift_residue_indices':[[idx%(p*o) for o in O] for idx in (C.h,C.shift)],
         'H':hh,'I':i,'W':w,'b':b,'delta':de,'delta_div_p_mod_p':unit,'unit_class':pow(unit,(p-1)//2,p)}
print(json.dumps(rows,indent=2))
