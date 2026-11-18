"""Reduction of the literal P=2R at all unramified, good, odd-support primes of r(0)."""
from math import isqrt,lcm,prod
import json
def factor(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out
def run(p,r,degree):
    def a(z,w=0):return (z%p,w%p)
    def add(x,y):return a(x[0]+y[0],x[1]+y[1])
    def sub(x,y):return a(x[0]-y[0],x[1]-y[1])
    def mul(x,y):return a(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    def div(x,y):
        v=pow((y[0]**2-2*y[1]**2)%p,-1,p);return mul(x,a(y[0]*v,-y[1]*v))
    root=a(0,1) if degree==2 else a(r)
    D=mul(sub(a(3),root),sub(a(3),root));R=add(a(1),root),mul(a(2),root)
    def plus(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P;u,v=Q
        if x==u and add(y,v)==a(0):return None
        s=div(sub(v,y),sub(u,x)) if x!=u else div(sub(mul(a(3),mul(x,x)),D),mul(a(2),y))
        z=sub(sub(mul(s,s),x),u)
        return z,sub(mul(s,sub(x,z)),y)
    def times(P,k):
        res=None
        while k:
            if k&1:res=plus(res,P)
            P=plus(P,P);k//=2
        return res
    assert mul(R[1],R[1])==mul(R[0],sub(mul(R[0],R[0]),D))
    P=plus(R,R);q=p**degree;M=isqrt(q+2+2*isqrt(q)+2)+2
    babies={};point=None
    for i in range(M):
        if i and point is None:ord=i;break
        babies[point]=i;point=plus(point,P)
    else:
        giant=point
        for j in range(1,M+1):
            if point in babies:
                ord=j*M-babies[point];break
            point=plus(point,giant)
        else:raise AssertionError
    assert times(P,ord) is None
    for t in factor(ord):assert times(P,ord//t) is not None
    return {'p':p,'residue_degree':degree,'sqrt2':r,'order_P':ord,
            'prime_divisors':factor(ord)}
def compute():
    ps=[5,163,661,733,1489,1861];rows=[]
    assert prod(ps)*4==4376874610839020
    for p in ps:
        assert factor(p)==[p]
        roots=[i for i in range(p) if i*i%p==2]
        if roots:
            for i in roots:rows.append(run(p,i,1))
        else:rows.append(run(p,None,2))
    H=lcm(*(j['order_P'] for j in rows));g=prod(ps)
    # bound for required Jd: p^(8+v_p(H)) over these six primes
    J=1
    for p in ps:
        a=H;v=0
        while a%p==0:v+=1;a//=p
        J*=p**(8+v)
    return {'orders':rows,'h_multiple':H,'h_factors':factor(H),'mandatory_Jd_divisor':str(J),'base_product':g}
if __name__=='__main__':print(json.dumps(compute(),indent=2))
