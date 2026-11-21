"""Sparse exact sieve for possible odd crossed-pole denominator primes."""
from math import isqrt
from pathlib import Path
import json,sys

cap = int(sys.argv[1]) if len(sys.argv)>1 else 65536
assert 2<=cap<=65536
raw = json.loads((Path(__file__).resolve().parent.parent/
    'rc-linked-scalar-specialization-publish-r1'/'EXACT-SCALAR-SPECIALIZATION.json').read_text())
h,J = raw['first_passing_h'],raw['J']
assert (h & -h)==2**6 and (J & -J)==2**7
S,R = 2**23,4376874610839020

def nonprime_witness(q):
    # Every rejection is individually a compositeness proof. No converse
    # or probabilistic claim about passing q is needed.
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if q!=p and q%p==0: return ('factor',p)
    d,s=q-1,0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17):
        x=pow(a,d,q)
        if x in (1,q-1):continue
        for j in range(s-1):
            x=x*x%q
            if x==q-1:break
        else:return ('strong_witness',a)
    return None

def sqrt2(q):
    d,s=q-1,0
    while d%2==0:d//=2;s+=1
    z=next((z for z in range(2,1000) if pow(z,(q-1)//2,q)==q-1),None)
    if z is None:raise ArithmeticError('no quadratic nonresidue found')
    x,b,g=pow(2,(d+1)//2,q),pow(2,d,q),pow(z,d,q)
    while b!=1:
        j=1;k=b*b%q
        while j<s and k!=1:j+=1;k=k*k%q
        if j>=s:raise ArithmeticError('Tonelli branch')
        t=pow(g,2**(s-j-1),q)
        x=x*t%q;g=t*t%q;b=b*g%q;s=j
    if x*x%q!=2:raise ArithmeticError('incorrect root')
    return x

def model(q,t):
    d=(3-t)%q; D=d*d%q; R0=((1+t)%q,2*t%q)
    assert (R0[1]**2 - R0[0]*(R0[0]**2-D))%q==0 and D
    def plus(P,Q):
        if P is None:return Q
        if Q is None:return P
        x,y=P; X,Y=Q
        if x==X:
            if (y+Y)%q==0:return None
            if y!=Y:raise ArithmeticError('not a field branch')
            ell=(3*x*x-D)*pow(2*y%q,-1,q)%q
        else:ell=(y-Y)*pow((x-X)%q,-1,q)%q
        x2=(ell*ell-x-X)%q
        return (x2,(ell*(x-x2)-y)%q)
    def scalar(m):
        P=None
        for c in bin(m)[2:]:
            P=plus(P,P)
            if c=='1':P=plus(P,R0)
        return P
    def pole(P):
        return P is not None and P[1]!=0 and (P[0]**2+D)%q==0
    return scalar,pole

candidates={}
for u in range(-isqrt(cap),isqrt(cap)+1):
    for v in range(1,isqrt(cap-u*u)+1):
        if (u-v)%2: continue
        a=1+S*u
        q=a*a+(S*v)**2
        assert q%2**24==1
        # In the rare case a composite has multiple representations, keep
        # every possible value of a to avoid unjustified order reduction.
        candidates.setdefault(q,[]).append((u,v,a))
counts={'candidates':len(candidates),'definitely_composite':0,'splitting_rejected':0,
        'models_checked':0,'no_h_pole':0,'both_h_poles':0,
        'h_pole_but_no_opposite_i_pole':0}
possible=[]
unresolved=[]
for q,uvs in sorted(candidates.items()):
    if nonprime_witness(q) is not None:
        counts['definitely_composite']+=1;continue
    # q is already 1 mod 2^24. The other two necessary signatures are fixed.
    if any(pow(a%q,(q-1)//2,q)!=1 for a in (7,-R)):
        counts['splitting_rejected']+=1;continue
    try:
        t=sqrt2(q)
        M=[model(q,t),model(q,-t%q)]
        poles=[pole(sc(h)) for sc,pole in M]
        counts['models_checked']+=1
        if poles == [False,False]:counts['no_h_pole']+=1;continue
        if poles == [True,True]:counts['both_h_poles']+=1;continue
        other=M[poles.index(False)]
        orders=[(q+1-2*a)*(q+1+2*a) for u,v,a in uvs]
        order=next((o for o in orders if all(sc(o) is None for sc,_ in M)),None)
        if order is None:raise ArithmeticError('no verified annihilator')
        i=(pow(6,15,order)*pow(3,65536,order)*(J%order))%order
        if not other[1](other[0](i)):
            counts['h_pole_but_no_opposite_i_pole']+=1;continue
        possible.append(dict(q=q,gaussian=uvs,root=t,source_h_poles=poles,order=order))
    except (ArithmeticError,ValueError,AssertionError) as e:
        unresolved.append(dict(q=q,detail=str(e)))
assert counts['candidates']==sum(counts[k] for k in
    ('definitely_composite','splitting_rejected','no_h_pole','both_h_poles',
     'h_pole_but_no_opposite_i_pole'))+len(possible)+len(unresolved)
n=cap+1
bound=S*S*n+1-isqrt(4*S*S*n)
print(json.dumps(dict(grid_cm_norm_cutoff=cap,counts=counts,
    surviving_crossed_residue_patterns=possible,unresolved=unresolved,
    outside_grid_prime_lower_bound=bound),indent=2))
