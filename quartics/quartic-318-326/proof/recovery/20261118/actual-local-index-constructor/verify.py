"""Lift reduction-order multiples of P modulo p^3 in an unramified ring; no CAS."""
from fractions import Fraction as F
from pathlib import Path
from math import gcd,prod,lcm
import json
def check(p,root,o):
    q=p**3
    def K(a,b=0):return (a%q,b%q)
    def add(x,y):return K(x[0]+y[0],x[1]+y[1])
    def sub(x,y):return K(x[0]-y[0],x[1]-y[1])
    def mul(x,y):return K(x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    def sq(x):return mul(x,x)
    def times(x,n):return K(n*x[0],n*x[1])
    def val(x):
        for a in range(3):
            if any(z%p**(a+1) for z in x):return a
        return 3
    if root is not None:
        root=(root-(root*root-2)*pow(2*root,-1,q))%q
        root=(root-(root*root-2)*pow(2*root,-1,q))%q
        assert (root*root-2)%q==0
    r=K(0,1) if root is None else K(root)
    d=sq(sub(K(3),r));R=(add(K(1),r),times(r,2),K(1))
    def double(Q):
        x,y,z=Q;a=sq(x);b=sq(y);c=sq(b);D=times(sub(sub(sq(add(x,b)),a),c),2)
        e=sub(times(a,3),mul(d,sq(sq(z))));f=sq(e);g=sub(f,times(D,2))
        return g,sub(mul(e,sub(D,g)),times(c,8)),times(mul(y,z),2)
    P=double(R)
    def plus(Q,V):
        x,y,z=Q;u,v,w=V;z2=sq(z);w2=sq(w);u1=mul(x,w2);u2=mul(u,z2)
        s1=mul(y,mul(w,w2));s2=mul(v,mul(z,z2));h=sub(u2,u1);rr=sub(s2,s1);h2=sq(h);h3=mul(h,h2);ww=mul(u1,h2)
        xx=sub(sub(sq(rr),h3),times(ww,2))
        return xx,sub(mul(rr,sub(ww,xx)),mul(s1,h3)),mul(h,mul(w,z))
    def scale(n):
        ret=P
        for a in bin(n)[3:]:
            ret=double(ret)
            if a=='1':ret=plus(ret,P)
        return ret
    x,y,z=scale(o);e=val(z)
    assert val(x)==val(y)==0 and 0<e<3
    if o%2==0:
        X,Y,Z=scale(o//2);assert val(Z)==0 and val(Y)>0
        zero_x=(val(X)>0)
    else:zero_x=False
    return (e,zero_x)
def main():
    data=json.loads(Path(__file__).with_name('ORDERS.json').read_text());tt=[]
    for row in data['orders']:
        dep,two=check(row['p'],row['sqrt2'],row['order_P'])
        tt.append([row['p'],row['sqrt2'],row['order_P'],dep,two])
    for p,r,o,deg in [(11,None,5,2),(17,6,5,1),(17,11,2,1)]:
        dep,two=check(p,r,o);tt.append([p,r,o,dep,two])
    H=lcm(64,data['h_multiple']);g=data['base_product'];J=H*g**8*11*17
    assert all(H%x[2]==0 and x[3]>=1 for x in tt)
    r=4*g;A=114444*r;m=11*g;beta=17*m
    assert m%8==m%3==m%17==1
    assert A==204**2*m
    def vp(a,p):
        z=0
        while a%p==0:z+=1;a//=p
        return z
    fp={}
    for p in [2,3,5,11,17,163,661,733,1489,1861]:
        gap=vp(J,p)-vp(H,p)+(21 if 6%p==0 else 0)+(65536 if p==3 else 0)
        vQ=2*gap-15*vp(r,p)
        assert vQ>0
        fp[str(p)]={'v_r':vp(r,p),'v_A':vp(A,p),'v_h':vp(H,p),'v_m_minus_v_h':gap,'v_Q':vQ}
    import real_enclosure
    boxes=real_enclosure.main()
    assert boxes[-1][1]<-10**13
    return {'formal_depths_and_half_is_zero_torsion':tt,'h':str(H),'J':str(J),'d':1,'A0':6,'B0':0,
       'm=n-1':'6^21 * 3^65536 * J','a':[0,-1],'local_calculations':fp,'real_enclosures_times_1e15':boxes,
       'scalar_squareclass':m,'beta':beta,'scope':'original label shape, all four guards, actual scalar Prepared, not full contact pattern'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
