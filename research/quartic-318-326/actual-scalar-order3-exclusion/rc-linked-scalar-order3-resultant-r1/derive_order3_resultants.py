#!/usr/bin/env python3
"""Fixed-degree eliminants for two residual h-orders dividing 3."""
from math import gcd,isqrt,prod
import json
import sympy as s
from sympy.ntheory import factorint
R=4376874610839020
beta=204618888056724185
A=17*144*beta
h=473592745039516333133760
rho=s.sqrt(2)
W,x=s.symbols("W x")
Q=s.QQ.algebraic_field(rho)
dom=Q.poly_ring(W)
p=lambda d,z:3-6*d*d*R*R*(z-1)**2-d**4*R**4*(z-1)**4
g1=p(3-rho,x)
# Direct polynomial w^4*g_conj(W/w), no inverse residue.
g2=3*x**4-6*(3+rho)**2*R**2*x*x*(W-x)**2-(3+rho)**4*R**4*(W-x)**4
rr=s.Poly(g1,x,domain=dom).resultant(s.Poly(g2,x,domain=dom))
one_side=s.Poly(p(3-rho,W),W,domain=Q)*s.Poly(p(3+rho,W),W,domain=Q)
G=s.Poly(rr,W,domain=Q)*one_side
assert G.degree()==24
assert all(a.is_Integer for a in G.all_coeffs())
G=s.Poly(G,W,domain=s.ZZ)
cont,G=G.primitive()
# All discarded content supported on 7R, certified by comparison with leading coeff.
assert G.LC()*cont==(7**4*R**8)**5
targets={"H":144*beta*W**4-(1+A)**2,
         "Lprime":7056*beta*W**4-48*(1+A)**2}
out={}
gcd_fixed=2*3*7*R*(1+A)*beta
Ig,Gparts=s.factor_list(G)
assert Ig==1 and sorted((g.degree(),e) for g,e in Gparts)==[(4,1),(4,1),(8,1),(8,1)]
def strip_fixed(n):
    a=n//gcd(n,gcd_fixed**n.bit_length())
    assert gcd(a,gcd_fixed)==1
    return a
known_small=set()
for name,f in targets.items():
    fp=s.Poly(f,W,domain=s.ZZ)
    r=abs(int(G.resultant(fp)))
    a=strip_fixed(r)
    pieces=[]
    for g,e in Gparts:
        v=strip_fixed(abs(int(g.resultant(fp))))
        # Bounded small-factor extraction, preserving unresolved binary chunks.
        fac=factorint(v,limit=10000)
        assert v==prod(int(p)**int(e) for p,e in fac.items())
        small={str(p):e for p,e in fac.items() if p<=5000000 and
               all(p%d for d in range(2,isqrt(p)+1))}
        known_small.update(map(int,small))
        pieces.append({"factor_degree":g.degree(),"exact_piece":str(v),
            "proven_small_prime_factors":small,
            "unresolved_factors_not_assumed_prime":{str(p):e for p,e in fac.items() if str(p) not in small}})
    assert a==prod(int(z["exact_piece"]) for z in pieces)
    out[name]={"raw_bit_length":r.bit_length(),
        "moving_bit_length":a.bit_length(),
        "pieces":pieces,
        "exact_moving_resultant":str(a)}

def order_screen(p):
    roots=[a for a in range(p) if a*a%p==2]
    data=[]
    for a in roots or [None]:
        c=lambda x,y=0:((x+(a or 0)*y)%p,y%p if a is None else 0)
        plus=lambda x,y:c(x[0]+y[0],x[1]+y[1]) if a is None else c(x[0]+y[0])
        neg=lambda x:c(-x[0],-x[1]) if a is None else c(-x[0])
        sub=lambda x,y:plus(x,neg(y))
        def mul(x,y):return ((x[0]*y[0]+2*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
        def inv(x):
            t=pow((x[0]**2-2*x[1]**2)%p,-1,p)
            return (x[0]*t%p,-x[1]*t%p)
        O=(0,0);d=c(3,-1);dd=mul(d,d)
        G=(c(1,1),c(0,2))
        def add(P,Q):
            if P is None:return Q
            if Q is None:return P
            u,v=P;x,y=Q
            if u==x and plus(v,y)==O:return None
            s=(mul(sub(mul(c(3),mul(u,u)),dd),inv(mul(c(2),v))) if u==x
               else mul(sub(y,v),inv(sub(x,u))))
            z=sub(sub(mul(s,s),u),x)
            return z,sub(mul(s,sub(u,z)),v)
        P=None
        for bit in bin(h)[2:]:
            P=add(P,P)
            if bit=='1':P=add(P,G)
        data.append({"root":a,"zero":P is None,"killed_by_3":add(add(P,P),P) is None})
    eligible=all(z["killed_by_3"] for z in data) and any(not z["zero"] for z in data)
    return {"p":p,"labels":data,"in_this_order3_locus":eligible}

print(json.dumps({"eliminant_degree":G.degree(),"discarded_content_bitlength":int(cont).bit_length(),
    "eliminant_coefficients":[str(a) for a in G.all_coeffs()], "resultants":out,
    "small_prime_screens":[order_screen(p) for p in sorted(known_small)]},indent=2))
