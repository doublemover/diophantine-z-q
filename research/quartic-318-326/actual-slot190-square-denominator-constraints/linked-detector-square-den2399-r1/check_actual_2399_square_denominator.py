#!/usr/bin/env python3
"""Finite certificate for the literal 2399 contact denominator obstruction."""
from math import gcd,isqrt
import json

def local_order_data(p):
    assert p>=3 and all(p%q for q in range(2,isqrt(p)+1))
    roots=[r for r in range(p) if (r*r-2)%p==0]
    assert len(roots)==2
    out=[]
    for r in roots:
        D=(3-r)**2%p
        R=((1+r)%p,2*r%p)
        assert ysq(R,p)==(R[0]**3-D*R[0])%p and R[1]
        def add(P,Q):
            if P is None: return Q
            if Q is None: return P
            x,y=P; X,Y=Q
            if x==X:
                if (y+Y)%p==0:return None
                v=(3*x*x-D)*pow(2*y,-1,p)%p
            else:v=(Y-y)*pow(X-x,-1,p)%p
            xx=(v*v-x-X)%p
            return xx,(v*(x-xx)-y)%p
        pts=[None,R]
        while pts[-1] is not None:
            pts.append(add(pts[-1],R))
            assert len(pts)<=(p+1)**2+2
        n=len(pts)-1
        mid=None if n%2 else pts[n//2]
        b=n//2 if mid==(0,0) else n
        out.append({'root':r,'order':n,'midpoint':mid,
                    'primary_modulus':n//gcd(n,2),'opposite_modulus':b})
    return out
def ysq(R,p):return R[1]**2%p

def run():
    p=2399
    sq={x*x%p for x in range(p)}
    A=(2,1,2399,407); B=(1,1,-1,32)
    assert not any((a*T+b)%p==0 for a,b in zip(A,B) for T in sq)
    vals=[(-b*pow(a,-1,p))%p if a%p else None for a,b in zip(A,B)]
    rows=local_order_data(p)
    pair=[gcd(a['primary_modulus'],b['opposite_modulus'])
          for a,b in (rows,rows[::-1])]
    assert [d['order'] for d in rows]==[300,80] and pair==[10,20]
    print(json.dumps({'p':p,'forbidden_nonzero_form_roots':vals,
                      'actual_order_rows':rows,'cross_gcds':pair},indent=2))

if __name__=='__main__':run()
