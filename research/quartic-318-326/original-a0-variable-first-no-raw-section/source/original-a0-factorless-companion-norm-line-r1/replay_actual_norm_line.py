#!/usr/bin/env python3
"""Literal archived scalar via small inert elliptic reductions, then exact norm-line checks."""
from math import isqrt, prod
from pathlib import Path
import json

S=json.loads(Path(__file__).with_name("PINNED-SCALAR-FIBER.json").read_text())
h,J,R,N=(S[k] for k in ("h","J","R_input","N"))
beta=114444*R//(17*12**2)
D=1+114444*R
assert h==473592745039516333133760 and N==65536
assert beta==204618888056724185 and D-1==17*12**2*beta
poles=(29,181,1346909,70850399941)
assert prod(poles)==D

def sign(x,p):
    return {0:0,1:1,p-1:-1}[pow(x%p,(p-1)//2,p)]

def shift_mod(n):
    return pow(6,15,n)*pow(3,N,n)*(J%n)%n

def source(p,ann):
    assert all(p%k for k in range(2,isqrt(p)+1))
    assert sign(2,p)==-1
    Z=(0,0); O=None
    def k(n):return n%p,0
    def add(a,b):return (a[0]+b[0])%p,(a[1]+b[1])%p
    def neg(a):return (-a[0])%p,(-a[1])%p
    def sub(a,b):return add(a,neg(b))
    def mul(a,b):return (a[0]*b[0]+2*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p
    def sq(a):return mul(a,a)
    def norm(a):return (a[0]**2-2*a[1]**2)%p
    def inv(a):
        n=pow(norm(a),-1,p)
        return a[0]*n%p,-a[1]*n%p
    d=sq((3,p-1))
    P=((1,1),(0,2))
    def on(T):
        if T is None:return True
        x,y=T
        return sq(y)==mul(x,sub(sq(x),d))
    assert on(P)
    def step(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P;z,w=Q
        if x==z:
            if add(y,w)==Z:return O
            assert y==w
            m=mul(sub(mul(k(3),sq(x)),d),inv(mul(k(2),y)))
        else:
            m=mul(sub(w,y),inv(sub(z,x)))
        xx=sub(sub(sq(m),x),z)
        T=xx,sub(mul(m,sub(x,xx)),y)
        assert on(T)
        return T
    def times(n):
        T=O
        for b in bin(n)[2:]:
            T=step(T,T)
            if b=="1":T=step(T,P)
        return T
    assert times(ann) is None
    h0,i0=h%ann,shift_mod(ann)
    H0,I0=times(h0),times(i0)
    row=dict(p=p,annihilator=ann,h_mod=h0,i_mod=i0,point_h=H0,point_i=I0)
    if H0 is None or I0 is None:
        assert H0 is None and I0 is None and R%p
        k=0
        while h%(p**(k+1))==0:k+=1
        assert shift_mod(p**k)==0
        m=(shift_mod(p**(k+1))//p**k)*pow(h//p**k,-1,p)%p
        Np=1
        Qp=m*m*pow(pow(R,15,p),-1,p)%p
        row.update(case="both formal", formal_ratio=m)
    else:
        def chart(T):
            x,y=T
            return mul(mul(k(2),y),inv(add(sq(x),d)))
        U,V=chart(H0),chart(I0)
        H,I=norm(U),norm(V)
        rr=pow(R,-1,p)
        Np=(1+(H*rr)**2+2*sq(U)[0]*rr)%p
        Qp=I*pow(H*pow(R,15,p),-1,p)%p
        row.update(case="regular",chart_h=U,chart_i=V,H=H,I=I)
    row.update(N=Np,Q=Qp,W=(Np*Np+R*Qp*Qp)%p)
    return row

rows=[]
for p,ann in zip(poles,(800,32724,1814161575200,5019779171659796018964)):
    r=source(p,ann); W=r["W"]
    assert D%p==0 and D//p%p and W
    c0=12*W*pow(D//p,-1,p)%p
    psi=lambda t:(beta*(3-beta*t*t)*(3*beta*t*t-1))%p
    r.update(c_stripped=c0,beta_mod=beta%p,c_depth=-1,lambda_depth=-2,
             lambda_stripped=(-beta*c0*c0)%p,lambda_unit_sign=sign(-beta,p),
             unrotated_F_sign=sign(-3*beta,p),
             rotated_t3_stripped_sign=sign(psi(3),p),
             rotated_t3_no_parameter_pole=(1-9*beta)%p!=0)
    assert r["rotated_t3_stripped_sign"]==1 and r["rotated_t3_no_parameter_pole"]
    rows.append(r)
assert [row["W"] for row in rows]==[12,146,429536,66349154550]
assert [r["unrotated_F_sign"] for r in rows]==[1,-1,-1,1]
assert rows[1]["lambda_unit_sign"]==-1
for old in S["normalizer_rows"]:
    new=next(r for r in rows if r["p"]==old["p"])
    for key in ["annihilator","chart_h","chart_i","H","I","W"]:
        assert new[key]==(tuple(old[key]) if isinstance(old[key],list) else old[key])

def full_rotation_row(p,ann):
    r=source(p,ann)
    assert D%p and r["W"]
    c=12*r["W"]*pow(D,-1,p)%p; b=beta%p; a=17*pow(100,-1,p)%p
    mu=b*c*c%p
    d=(1+3*a*a*mu)%p
    candidates=[]
    for e,f in [(1,1),(1,-1),(-1,1),(-1,-1)]:
        A=(1+(e*a+3*f*a+3*e*f*a*a)*mu)*pow(d,-1,p)%p
        B=c*(1+e*a+3*f*a+3*e*f*a*a*mu)*pow(d,-1,p)%p
        for t in (3,-3):
            dd=pow(1-b*t*t,-1,p)
            AA=(A*(1+b*t*t)+2*b*B*t)*dd%p
            BB=(B*(1+b*t*t)+2*A*t)*dd%p
            F=(4*AA*AA-3*b*BB*BB)%p
            candidates.append(dict(epsilon1=e,epsilon2=f,t=t,A=A,B=B,A_t=AA,B_t=BB,F=F,sign=sign(F,p)))
    r.update(c=c,beta_mod=b,a=a,mu=mu,seed_denominator=d,candidates=candidates)
    return r
r13=full_rotation_row(13,180)
r19=full_rotation_row(19,400)
assert (r13["c"],r13["W"],r13["formal_ratio"])==(8,1,0)
assert (r19["c"],r19["W"],r19["formal_ratio"])==(1,2,5)
assert [x["F"] for x in r13["candidates"]]==[1,5,5,1,5,5,1,12]
assert [x["F"] for x in r19["candidates"]]==[14,7,2,15,2,17,14,14]
assert all(-1 in (u["sign"],v["sign"]) for u,v in zip(r13["candidates"],r19["candidates"]))
print(json.dumps(dict(scope="fixed original h and J; fixed first chart; no affine rational point or arbitrary-rotation exclusion",
                      h=h,N=N,beta=beta,D=D,pole_rows=rows,unit_rotation_tests=[r13,r19]),
                 indent=2,sort_keys=True))
