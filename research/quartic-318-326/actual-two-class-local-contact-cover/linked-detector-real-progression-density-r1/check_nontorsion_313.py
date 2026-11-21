#!/usr/bin/env python3
"""Independent first-return replay for the two literal 313 reduction arms."""
import json
from math import isqrt
p=313
assert all(p%k for k in range(2,isqrt(p)+1))
roots=[r for r in range(p) if r*r%p==2]
assert len(roots)==2
out=[]
for r in roots:
    d=(3-r)%p
    a=-d*d%p
    assert d and (64*d**6)%p
    R=((1+r)%p,(2*r)%p)
    def on(P):
        return P is None or (P[1]**2-P[0]**3-a*P[0])%p==0
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P; X,Y=Q
        if x==X:
            if (y+Y)%p==0:return None
            assert y==Y
            s=(3*x*x+a)*pow(2*y,-1,p)%p
        else:s=(Y-y)*pow(X-x,-1,p)%p
        xx=(s*s-x-X)%p
        T=xx,(s*(x-xx)-y)%p
        assert on(T)
        return T
    assert on(R)
    Rn=None; chain=[]
    for n in range(1,p+1+2*isqrt(p)+2):
        Rn=add(Rn,R);chain.append(Rn)
        if Rn is None:break
    else:raise AssertionError('no first return')
    out.append({'root':r,'d':d,'R':R,'first_order':n,'multiples':chain})
assert sorted(x['first_order']for x in out)==[6,17]
print(json.dumps({'prime':p,'arms':out},indent=2))
