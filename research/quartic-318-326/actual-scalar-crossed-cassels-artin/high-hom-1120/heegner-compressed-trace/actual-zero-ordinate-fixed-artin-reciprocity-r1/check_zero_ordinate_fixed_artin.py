#!/usr/bin/env python3
from math import gcd,prod,isqrt
import json

B=204618888056724185
K=1+2448*B
fixed_den=[29,181,1346909,70850399941]
assert prod(fixed_den)==K
# Literal compact same-scalar c mod p and delta/p mod p from the four
# pinned actual theta places; the cited donor gives their modular replays.
visible=[(131,54,82),(6551,2194,684),(2470991,722614,2223081),(16782959,9763981,13715188)]
data=[
    (2952271997968816765,31859917667562016618135,59323292900802,9995282212057),
    (5566083893370034,131334033162619006246327,275139103369479,562104197612846)]
assert gcd(data[0][3],data[1][3])==1

def trial(p):
    return p>1 and all(p%q for q in range(2,isqrt(p)+1))
assert all(trial(p) for p in fixed_den+[p for p,_,_ in visible])
def leg(a,p):
    a=pow(a%p,(p-1)//2,p)
    assert a in [1,p-1]
    return 1 if a==1 else -1

def hil(p,a,k,b,l):
    return leg((-1)**(k*l)*a**l*b**k,p)

P=1186981
assert trial(P)
r=547597
assert (r*r-B)%P==0
rows=[]
for S,x,y,z in data:
    assert x*x-B*y*y==S*z*z and gcd(gcd(x,y),z)==1
    assert gcd(S,K)==1 and x>0 and S>0
    dyadic=(-1)**(S%2==0)
    fden=[leg(S,p) for p in fixed_den]
    F=[dyadic,prod(fden)]
    H=[]
    for p,c,u in visible:
        assert z%p and (1-B*c*c)%p==0 and u%p
        s=-pow(c,-1,p)%p
        s2=s+((B-s*s)//p)*pow(2*s,-1,p)%p*p
        assert (s2*s2-B)%(p*p)==0
        V=[(x+y*s2)%(p*p),(x-y*s2)%(p*p)]
        depths=[int(v%p==0) for v in V]
        assert sum(depths)==int(S%p==0)
        unit0,unit1=[w//p**t%p for w,t in zip(V,depths)]
        h0=hil(p,u*pow(2,-1,p)%p,1,unit0,depths[0])
        h1=hil(p,2,0,unit1,depths[1])
        F.append(h0*h1)
        H.append(dict(p=p,gamma_zero_root=s,sigma_residues=V,sigma_depths=depths,hilbert_arms=[h0,h1]))
    assert leg(S,P)==1
    test=[leg(x+y*v,P) for v in (r,P-r)]
    assert test==[-1,-1]
    rows.append(dict(S=S,norm_coordinates=[x,y,z],dyadic=dyadic,
         normalizer_signs=fden,visible=H,fixed_factors=F,
         fixed_product=prod(F),auxiliary_Artin_both_arms=test))
assert [t['fixed_product'] for t in rows]==[1,-1]
print(json.dumps(dict(beta=B,known_normalizer=fixed_den,
   auxiliary=[P,r],tables=rows,scope='exact fixed phases; literal unseen Artin products not evaluated'),sort_keys=True,indent=2))
