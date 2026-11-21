#!/usr/bin/env python3
"""Small finite controls. They check literal algebra, not isogeny or a Lean build."""
from random import Random

rng = Random(318326)

def w_of_t(t, p, n):
    w = 0
    m = p
    for _ in range(1, n):
        m *= p
        roots = [(w+k*(m//p)) % m for k in range(p)
                 if ((w+k*(m//p)) + t*(w+k*(m//p))**2 - t**3) % m == 0]
        assert len(roots) == 1
        w, = roots
    return w

def add(A, B, m):
    t,w = A
    T,W = B
    l = (T*T+t*T+t*t-w*w) * pow((1+T*(W+w))%m, -1, m) % m
    v = (w-l*t) % m
    c = 2*l*v*pow((1-l*l)%m,-1,m) % m
    s = (c-t-T) % m
    z = (l*s+v) % m
    assert (l*T+v-W)%m==0
    assert (z+s*z*z-s**3)%m==0
    return (-s%m,-z%m), c

def val(x,p,n):
    if x == 0:
        return n
    i = 0
    while x%p==0:
        x//=p
        i+=1
    return i

counts = dict(charts=0,chords=0,tangent=0,negation=0,turn=0,multiplication=0,affine_lifts=0,
              affine_secants=0,y0_secants=0)
for p in (3,5,7,11,13,17):
    for n in (2,3,4,5):
        m=p**n
        ts = [p*rng.randrange(m//p) for _ in range(150)] + [0,p,m-p,p**(n-1)]
        S = [(t,w_of_t(t,p,n)) for t in ts]
        i = next((r for r in range(m) if (r*r+1)%m==0),None) if p%4==1 else None
        for t,w in S:
            rho = t*w%m
            assert (rho*rho+rho-t**4)%m==0 and (rho%p)==0
            assert t**3*pow(1+rho,-1,m)%m==w
            counts['charts']+=1
            if i is not None:
                assert w_of_t(i*t%m,p,n)==-i*w%m
                counts['turn']+=1
            T = (t,w)
            S2,_ = add(T,T,m)
            assert S2[1]==w_of_t(S2[0],p,n)
            counts['tangent']+=1
            assert add(T,(-t%m,-w%m),m)[0]==(0,0)
            counts['negation']+=1
            cur=(0,0)
            for q in range(1,2*p+2):
                cur,c=add(cur,T,m)
                assert (cur[0]-q*t)%p**min(n,5*val(t,p,n))==0
                assert c%p**min(n,5*val(t,p,n))==0
                if t!=0 and q%p!=0:
                    assert cur[0]!=0 and val(cur[0],p,n)==val(t,p,n)
                counts['multiplication']+=1
        for A,B in zip(S,reversed(S)):
            C,c=add(A,B,m)
            assert c%p**min(n,5*min(val(A[0],p,n),val(B[0],p,n)))==0
            assert C[1] == w_of_t(C[0],p,n)
            counts['chords']+=1
    # Use two-digit ordinary affine lifts. For y_bar=0 and x1 != x2 modulo p^2,
    # val(y1-y2), val(y1+y2) and val(x1-x2) determine slope sign (if distinguishable).
    m=p**3
    for x in range(p):
        for y in range(p):
            if (y*y-x**3+x)%p: continue
            if y==0:
                assert x in (0,1,p-1)
                assert (3*x*x-1)%p!=0
            points=[]
            for k in range(p):
                a=x+p*k
                for l in range(p):
                    b=y+p*l
                    if (b*b-a**3+a)%(p*p)==0:
                        # Lift in the simple coordinate independently.
                        if y:
                            bs=[b+p*p*j for j in range(p) if ((b+p*p*j)**2-a**3+a)%m==0]
                            assert len(bs)==1
                            points.append((a,bs[0]))
                        else:
                            aa=[a+p*p*j for j in range(p) if (b*b-(a+p*p*j)**3+(a+p*p*j))%m==0]
                            assert len(aa)==1
                            points.append((aa[0],b))
            assert len(points)==p
            counts['affine_lifts']+=len(points)
            for a,b in points:
                for A,B in points:
                    if a==A: continue
                    D=(a*a+a*A+A*A-1)%m
                    assert ((b-B)*(b+B)-(a-A)*D)%m==0
                    if y:
                        assert val((b+B)%m,p,3)==0 < val((a-A)%m,p,3)
                        counts['affine_secants']+=1
                    else:
                        assert D%p
                        assert val((b+B)%m,p,3)<val((a-A)%m,p,3)
                        counts['y0_secants']+=1
for k,v in counts.items(): print(f"{k}={v}")
