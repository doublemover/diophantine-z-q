#!/usr/bin/env python3
"""Exact p=17 obstruction for the surviving numerical same-scale mark."""
from pathlib import Path
from hashlib import sha256
P=Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py'
raw=P.read_bytes()
assert sha256(raw).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(raw.decode().split('\nqs=(')[0],globals())
a,b=67845285152401,292887266126401
p=17; M=p*p
arms=[]
for r in (6,11):
    rho=r+p*((2-r*r)//p*pow(2*r,-1,p)%p)
    order,P,U,formal=F0(p,rho);o=order()
    ls=labels(p*o)
    uu=[U(P(n))[0] for n in ls]
    assert all(u%p for u in uu)
    ar=prod(-pow(u,-1,M) for u in uu)%M
    arms.append(dict(r=r,rho=rho,order=o,labels=ls,U_p2=uu,A=ar))
pA,pB=[r['A'] for r in arms]
c=[1,((pA+pB)*pow(2,-1,M)+pA*pB)%M,pA*pB%M]
assert c==[1,216,84] and vp(c[2]**2-1,p)==1 and all(x%p for x in c)
assert chi(a,p)==chi(b,p)==-1
s,t=(mod(F(-32,407),p),mod(F(1,2399),p))
roots=[mod(F(j),p) for j in (0,F(-1,2),-1,F(-32,407),F(1,2399))]
assert set(roots)=={0,16,8,15,9}
assert s==15 and t==9
rows=[]
for X in sorted({w*w%p for w in range(p)}):
    aval,bval=(chi(X-s,p),chi(X-t,p))
    T=[X*(cj*pow(c[1],-1,p))**2%p for cj in c]
    FV=[prod(z-r for r in roots)%p for z in T]
    Fbit=[chi(v,p) for v in FV]
    rows.append(dict(W_squared=X,conic_signs=[aval,bval],literal_T=T,F_values=FV,F_signs=Fbit,
         compatible_B=all(x in (-1,0) for x in (aval,bval))))
assert [r['W_squared'] for r in rows if r['compatible_B']]==[4,9,15]
target={u['W_squared']:u for u in rows}
assert target[4]['F_signs'][1]==target[15]['F_signs'][0]==-1
assert target[9]['literal_T']==[16,9,16]
assert target[1]['literal_T']==[15,1,15] and target[8]['literal_T']==[1,8,1]
assert target[0]['conic_signs']==[1,1]
print(json.dumps(dict(p=p,retuned_literal_J=J,a_b_mod_p=[a%p,b%p],arms=arms,
          c_mod_p2=c,v17_c2sq_minus_one=1,roots=roots,square_values=rows),indent=2))
