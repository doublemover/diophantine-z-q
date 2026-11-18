"""Exact rational witness and independently checkable arithmetic of a canonical-anchor obstruction."""
from fractions import Fraction as F
from itertools import product
from math import prod,gcd
import json
N=6953;beta=17;theta=409
def chi(a,p):
    assert a%p
    return 1 if pow(a%p,(p-1)//2,p)==1 else -1
def vunit(x,p):
    assert x;k=0
    while x%p==0:k+=1;x//=p
    return k,x
def bitpair(a):
    return {1:(0,0),3:(1,1),5:(0,1),7:(1,0)}[a%8]
def local(a,b):
    if (a>0)!=(b>0):return False
    va,ua=vunit(a,2);vb,ub=vunit(b,2);sa,fa=bitpair(ua);sb,_=bitpair(ub)
    if (va%2) or (sa+vb)%2 or (fa+sb+vb)%2:return False
    v,w=vunit(b,3)
    if v%2 or chi(w,3)!=1:return False
    for p in (17,409):
        va,ua=vunit(a,p);vb,ub=vunit(b,p);c=N//p
        if chi(ua,p)*chi(c,p)**(va%2)*chi(-3,p)**(vb%2)!=1:return False
        if chi(ub,p)*chi(-c,p)**(vb%2)!=1:return False
    return True
def hilbert2(a,b):
    u,x=vunit(a,2);v,y=vunit(b,2)
    return (-1)**(((x-1)//2*((y-1)//2)+u*((y*y-1)//8)+v*((x*x-1)//8))%2)
def cubic(e,x):return x*(x-e)*(x+3*e)
def fmt(x):return str(x)
def main():
    a=12;e=53;l=1073;b=F(204,1073)**2;D=1-b/17
    assert beta*a*a+theta*e*e==l*l and gcd(a,gcd(e,l))==1 and D==theta*F(e,l)**2
    assert (409,17)==(theta,beta) and theta*beta==N and N%24==17
    assert all(all(p%q for q in range(2,int(p**0.5)+1)) for p in (17,409))
    assert 0<b<17 and [vunit(b.numerator,p)[0]-vunit(b.denominator,p)[0] for p in (2,3,17)]==[4,2,2]
    B=17*b;V=B**2*D
    E=F(2014880256,4864365025);S=F(-1424848608,2768946245)
    y1=F(-2495222615232,5219463671825);y2=F(-115188947076336604087118173483290329088,4411321710125745115338446056112360723825)
    assert E*S*y1*y2 and y1*y1==cubic(E,B) and y2*y2==cubic(E*V,B*S*S)
    # Reconstruct using the independent source-parameter route, not just a table of outputs.
    def t(l):return (l*l-3*beta)/(2*l),(l*l+3*beta)/(2*l)
    s,J=t(F(17,9));t,K=t(F(81));h=(s-t)/(s*t-beta);w=17*h;b0=w*w;B0=17*b0;d=1-b0/17
    assert h==F(9,89) and d==theta*F(4,89)**2
    T=K*(s*s-beta)/(J*(s*t-beta));es=(s*s-beta)/J**2;E0=B0*es;S0=B0*T
    Y=w**3*beta*(4*beta*s/J**2);Z=(w*S0)**3*beta*(4*beta*t/K**2)
    X=F(356,3219);H=F(4717,4292)
    assert b==b0*X*X and D==d*H*H and (E,S,y1,y2)==(E0*X**2,S0*X**2*H,Y*X**3,Z*X**9*H**3)
    # Classical full-descent local support over all 32 signed squareclasses.
    basis=(-1,2,3,17,409);scl=[prod(g**c for g,c in zip(basis,bits)) for bits in product((0,1),repeat=5)]
    Sel={(a,b) for a in scl for b in scl if local(a,b)}
    assert len(Sel)==32 and sorted(b for a,b in Sel if a==409)==[1,409] and (-1,-2) in Sel
    # The difference (1,409) is actually represented, with explicit descent roots.
    x0=F(1218087481,14596605);x=x0*x0;B1=F(2384152,14596605);B2=F(120390298,14596605)
    assert x-N==theta*B1**2 and x+3*N==theta*B2**2
    y=x0*theta*B1*B2;assert y*y==cubic(N,x)
    # Formula for alpha=(theta,1), against epsilon=(-1,-2), in PAIRING.md.
    xE,yE=-1,-2;ell=2*l*5
    hleft=hilbert2(ell,xE);hright=hilbert2(-ell,xE*yE)
    factors={'2':hleft*hright,'3':(-1)**(vunit(xE,3)[0]%2),'infinity':1}
    for p in (17,409):
        vx=vunit(xE,p)[0]%2;vy=vunit(yE,p)[0]%2
        factors[str(p)]=(chi(-1,p)**vx*chi(-2*l,p)**vy if p==beta else chi(-2,p)**vx*chi(-3*l,p)**vy)
    assert (hleft,hright)==(1,-1) and prod(factors.values())==-1
    return dict(b=str(b),complement=str(D),E=str(E),S=str(S),y1=str(y1),y2=str(y2),seed_parameters=['17/9','81'],depths=[4,2,2],
        curve_N=N,full_selmer_pairs=len(Sel),first409_lifts=[[409,1],[409,409]],rational_difference=[str(x),str(y)],
        pairing_args=[xE,yE],dyadic_factors=[hleft,hright],local_pairing_factors=factors,pairing_product=prod(factors.values()))
if __name__=='__main__':print(json.dumps(main(),indent=2))
