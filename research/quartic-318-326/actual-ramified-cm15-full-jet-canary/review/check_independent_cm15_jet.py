from fractions import Fraction as Q
from sympy import symbols, groebner, expand
e,r=symbols("e r")
G=groebner([e**2-5,r**2+3],e,r,domain="QQ")
def red(f):
    n,d=f.as_numer_denom()
    n,d=G.reduce(expand(n))[1],G.reduce(expand(d))[1]
    res=1
    for ei,ri in [(-e,r),(e,-r),(-e,-r)]:res=G.reduce(expand(res*d.subs({e:ei,r:ri},simultaneous=True)))[1]
    dd=G.reduce(expand(d*res))[1]
    assert len(dd.free_symbols)==0 and dd
    return G.reduce(expand(n*res/dd))[1]
for sign in (1,-1):
    a1=red((-49-21*e+sign*r*(495+231*e))/4)
    a2=red((-49-21*e-sign*r*(495+231*e))/4)
    l=[a1,red(4096/a2),a1,red(4096/a2),a1]
    # Independently solve B=C²+kC within the coefficient field using
    # first arrow consistency; C expression then checked in both equations.
    for h,k in ((16,16),(4,8),(2,4)):
        next=[]
        for a,b in zip(l,l[1:]):
            c=red((b-h*a)/(a+k))
            assert red(c*(c+k)-b)==red(c*c-a*(c+h))==0
            next.append(c)
        l=next
    X,Y=red(l[1]+2),(1+sign*e*r)/2
    Xs=red(X.subs({e:-e,r:-r},simultaneous=True))
    assert red(X**3+4*X-Y**2)==0
    slope=red((Y+Y)/(X-Xs))
    xc=red(slope*slope-X-Xs); yc=red(slope*(X-xc)-Y)
    assert (xc,yc)==(1,e)
    # dX/(2Y) has residue coefficient obtained by exact derivative at e=0.
    D1=red(X.diff(e)).subs(e,0); D2=red(Xs.diff(e)).subs(e,0)
    assert red(8*(D1-D2))==4
P=(Q(25,4),-Q(75,8))
for _ in range(2):
    x,y=P
    lam=(3*x*x-25)/(2*y); xx=lam**2-2*x
    P=xx,(-y+lam*(x-xx))
    assert P[1]**2==P[0]**3-25*P[0]
def mod(f): return f.numerator*pow(f.denominator,-1,5)%5
assert tuple(map(mod,P))==(1,1)
assert mod(-P[0]/P[1])==4
# Short Vélu kernel: at the reduced first arrow R=-1,
# v=3rho. Reduced second kernel is R+2v=-1+rho.
Rp=-1
Rpp=-1+r
G5=groebner([r*r-2],r,modulus=5)
c=G5.reduce(expand(-2*(3*Rp**2+3*Rpp**2)))[1]
assert G5.reduce(expand(c-(1+2*r)))[1]==0
assert G5.reduce(expand(c*r*3-2*(1-r)))[1]==0 # (-3)^-1 = 3 mod 5
print('Both literal orientations: P−σP=(1,e), 8 signed invariant tangent=4. [4] on E5 residue=(1,1), cusp −X/Y=4. Vélu c=1+2rho.')
