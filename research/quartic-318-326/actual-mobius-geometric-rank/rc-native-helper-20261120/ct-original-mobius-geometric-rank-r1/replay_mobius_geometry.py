"""Exact polynomial, geometric-section and specialized torsion controls."""
from fractions import Fraction as Q
from math import isqrt
import json

def inv(a,b): return 16*(a*a-3*b),16*b*b*(a*a-4*b)
def data(u):
    d=1-u
    a=9*u-41*u*u
    b=16*u**3*(25*u-9)
    return a,b,-2*a,(9*u*d)**2
def test_section(u):
    d=1-u
    a,b=2*(41*u-9),81*d*d
    x,y=25*d*d,5*d*d*(25*u+16)
    assert x*(x*x+a*x+b)==y*y
    return x,y
def on(P,a,b):
    if P is None: return True
    x,y=P
    return y*y==x*(x*x+a*x+b)
def add(P,R,a,b):
    if P is None: return R
    if R is None: return P
    x,y=P; z,w=R
    if x==z and y==-w: return None
    m=(w-y)/(z-x) if x!=z else (3*x*x+2*a*x+b)/(2*y)
    t=m*m-a-x-z
    S=(t,m*(x-t)-y)
    assert on(S,a,b)
    return S

# Both discriminant/c4 comparisons have degree at most 12 and the section
# equation has degree <=6 in u; the thirteen distinct samples are identities.
for n in range(-6,7):
    u=Q(n)
    a,b,ap,bp=data(u); d=1-u; f=25*u-9
    c4,disc=inv(a,b); c4p,discp=inv(ap,bp)
    assert c4==16*u*u*((9-41*u)**2-48*u*f)
    assert c4p==16*u*u*(4*(41*u-9)**2-243*d*d)
    assert disc==16*16**2*9**2*u**8*d*d*f*f
    assert discp==16*81**2*256*u**7*d**4*f
    test_section(u)
assert (19-2-4*3-4)==(19-2-2*7-2)==1
u=Q(1,2)
x,y=test_section(u)
P=(4*x,8*y); a,b=Q(92),Q(324)
assert P==(25,285) and on(P,a,b)
Q2=add(P,P,a,b)
assert Q2[0]==Q(301,570)**2
assert (9*Q2[0]+3*a).denominator%5==0

# Real specialization where the 2-primary torsion really grows.
beta,theta=3,13
c,e=Q(2,5),Q(1,5)
u,d=beta*c*c,theta*e*e
assert u+d==1
_,_,ap,bp=data(u)
R=(-Q(324,625),Q(0)); R2=(-Q(6084,625),Q(0))
T=(Q(0),Q(0)); F=(9*u*d,8*u*(9*u*d))
assert on(F,ap,bp) and on(R,ap,bp) and on(R2,ap,bp)
assert add(R,R2,ap,bp)==T
assert add(F,F,ap,bp)==T
S=add(F,R,ap,bp); S2=add(F,R2,ap,bp)
assert S[0]<0 and S2[0]<0
assert add(S,S,ap,bp)==T and add(S2,S2,ap,bp)==T
assert F[0]/(beta*theta)==Q(6,25)**2
assert isqrt(beta*theta)**2!=beta*theta

print(json.dumps({
 "geometric_fields":{"J_fibres":{"I4":4,"I2":4},"J_prime_fibres":{"I8":2,"I2":2,"I1":4},
                     "Picard_number":19,"root_rank":16,"MW_rank":1},
 "non_torsion_control":{"mu":"1/2","integral_curve_a_b":[92,324],
                        "P":[25,285],"x_2P":str(Q2[0]),
                        "short_model_x_2P":str(9*Q2[0]+3*a)},
 "torsion_growth_toy":{"beta":beta,"theta":theta,"c":str(c),"e":str(e),
                       "extra_2_torsion_x":list(map(str,[R[0],R2[0]])),
                       "x_order4_other_translates":list(map(str,[S[0],S2[0]])),
                       "x_positive_order4":str(F[0]),
                       "not_an_original_pole":True},
 "symbolic_polynomial_verification_sample_count":13},indent=2,sort_keys=True))
