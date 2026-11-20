#!/usr/bin/env python3
"""Compute the fixed original scalar independently by exact finite-field point counting."""
from math import isqrt, prod
import sys

B=prod([5,11,17,163,661,733,1489,1861])
assert B==204618888056724185
A=17*B*12**2
R=4*B//(11*17)
assert 11*17*R==4*B
h=473592745039516333133760
J=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000
i=6**15*3**65536*J
m, rem=divmod(i,h)
assert rem==0 and m%4==0
primes=[11,13,17,19,23,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,167,173,179,191,193,197,199,211,223,227,229,233,239,241]

def field_side(p, root):
    # Integers encode c+ds, where s²=2; split side uses ints modulo p.
    if root is None:
        cn=lambda c,d=0:c%p+p*(d%p)
        def add(x,y): return cn(x%p+y%p,x//p+y//p)
        def sub(x,y): return cn(x%p-y%p,x//p-y//p)
        def mul(x,y):
            a,b=x%p,x//p;c,d=y%p,y//p
            return cn(a*c+2*b*d,a*d+b*c)
        def inv(x):
            a,b=x%p,x//p; t=pow((a*a-2*b*b)%p,-1,p)
            return cn(a*t,-b*t)
        q=p*p
    else:
        cn=lambda c,d=0:(c+d*root)%p
        add=lambda a,b:(a+b)%p
        sub=lambda a,b:(a-b)%p
        mul=lambda a,b:a*b%p
        inv=lambda a:pow(a,-1,p)
        q=p
    sq=lambda x:mul(x,x)
    d=sq(cn(3,-1));assert d!=0 and p!=2
    g=cn(1,1),cn(0,2)
    squares={0:1}
    for y in range(1,q):
        y2=sq(y)
        squares[y2]=squares.get(y2,0)+1
    assert set(squares.values())=={1,2} and len(squares)==1+(q-1)//2
    rhs=lambda x:mul(x,sub(sq(x),d))
    assert sq(g[1])==rhs(g[0])
    order=1+sum(squares.get(rhs(x),0) for x in range(q))
    def ap(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P; xp,yp=Q
        if x==xp and add(y,yp)==0:return None
        l=(mul(sub(yp,y),inv(sub(xp,x))) if x!=xp
           else mul(sub(mul(cn(3),sq(x)),d),inv(mul(cn(2),y))))
        X=sub(sub(sq(l),x),xp)
        Y=sub(mul(l,sub(x,X)),y)
        assert sq(Y)==rhs(X)
        return X,Y
    def times(k):
        P=None
        for a in bin(k)[2:]:
            P=ap(P,P)
            if a=='1':P=ap(P,g)
        return P
    assert times(order) is None
    def chart(P):
        if P is None:return 0
        x,y=P
        den=add(sq(x),d)
        assert den!=0, (p,root,P)
        return mul(mul(cn(2),y),inv(den))
    P,Q=times(h%order),times(i%order)
    u,v=chart(P),chart(Q)
    if u!=0:ratio=mul(v,inv(u))
    else:
        assert v==0
        # Translation by T=(0,0) preserves U; translation by the other
        # nonidentity 2-torsion has U/parameter linear coefficient negated.
        assert P is None or P[1]==0
        ratio=cn(m if P is None or P[0]==0 else -m)
    return u,ratio,order,u==0

for p in primes:
    assert p>7 and all(p%j for j in range(2,isqrt(p)+1))
    assert (1+A)*R%p!=0
    roots=[x for x in range(p) if x*x%p==2]
    sides=[field_side(p,r) for r in (roots or [None])]
    if roots:
        (a,b),(u,v)=[(x[0],x[1]) for x in sides]
        N=(1+a*a*pow(R,-1,p))*(1+u*u*pow(R,-1,p))%p
        Q=b*v*pow(R,-15,p)%p
    else:
        ((u,ratio,order,f),)=sides
        a,b=u%p,u//p
        # Norm(1+u²/R) in F_p[√2].
        g=pow(R,-1,p)
        N=((1+(a*a+2*b*b)*g)**2-2*(2*a*b*g)**2)%p
        Q=((ratio%p)**2-2*(ratio//p)**2)*pow(R,-15,p)%p
    W=(N*N+R*Q*Q)%p
    c=12*W*pow(1+A,-1,p)%p
    print(p,c)
    if '--verbose' in sys.argv: print(p,c,sides,file=sys.stderr)
