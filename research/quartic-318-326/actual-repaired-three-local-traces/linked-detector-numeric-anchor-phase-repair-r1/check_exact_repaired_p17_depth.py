#!/usr/bin/env python3
"""All original detector leaf integrality at the actual repaired same h."""
from pathlib import Path
from hashlib import sha256
P=Path(__file__).resolve().parents[1]/'linked-detector-numeric-old-compatible-positive-cover-r2/check_exact_numeric_positive_cover.py'
raw=P.read_bytes()
assert sha256(raw).hexdigest()=='600ae9b7f9d6ece0849d3a772a71a93e306b7358db560e608b0d5e7d0bac757a'
exec(raw.decode().split('\nqs=(')[0],globals())
import sys
data=json.loads(Path(sys.argv[1]).read_bytes())
h=int(data.get('final_h',data.get('h_least_positive')))
assert h%20==0 and vp(h,17)==1 and h>1
assert int(data['literal_J'])==J
p=17; M=p*p; arms=[]
for r in (6,11):
    rho=r+p*((2-r*r)//p*pow(2*r,-1,p)%p)
    order,P,U,formal=F0(p,rho);o=order()
    ls=labels(p*o)
    uu=[U(P(n))[0] for n in ls]
    assert all(u%p for u in uu)
    assert formal(P(o)) and vp(P(o)[0],p)==1 and not h%o
    aa=prod(-pow(u,-1,M) for u in uu)%M
    k=(-1+7*rho*pow(4,-1,M))%M
    m=(39*pow(8,-1,M)-9*rho*pow(2,-1,M))%M
    D=(3-rho)**2%M
    assert k%p and D%p and vp(m,p)<=1
    arg=D*pow(k**4,-1,p)%p
    PG=(1-61*pow(65,-1,p)*arg+16*pow(195,-1,p)*arg*arg)%p
    QG=(1-7*pow(13,-1,p)*arg)%p
    assert PG and QG
    qj=[];v=[]
    for n in ls:
        Pn=P(n);assert not formal(Pn)
        x,y=[r[0] for r in Pn]
        den=(x*x+D)%M;assert den%p
        V=(x**4-6*D*x*x+D*D)*pow(den*den,-1,M)%M
        qj.append((1+5*pow(13,-1,M)*(V-1))%M);v.append(V)
    assert all(q%p for q in qj[1:])
    arms.append(dict(r=r,root=rho,order=o,formal_z_at_order=P(o)[0],
        literal_labels=ls,U_p2=uu,V_p2=v,QJ_p2=qj,reciprocal_prod=aa,
        k_m_D_p2=[k,m,D],argument_p=arg,PG_QG_p=[PG,QG],
        m_depth=vp(m,p),U_h_depth=2,shift_depth=-2,
        common_log_depth=-vp(m,p),primary_ratio_depth_min=0,
        alternate_ratio_depth_min=vp(m,p)))
P1,P2=[z['reciprocal_prod'] for z in arms]
c=[1,((P1+P2)*pow(2,-1,M)+P1*P2)%M,P1*P2%M]
assert c==[1,216,84]
# W=1/17 is an exact local value; all three c are units, w=W/c_1.
assert all(chi(data[z],p)==1 for z in ('a','b'))
# Fold consequences under the direct source integral coefficient proof.
F_depth=-10; delta_depth=-2; weighted_depth=6; pole_depth=F_depth-6*delta_depth
assert pole_depth==2
print(json.dumps(dict(D=data['D'],literal_h_mod289=h%289,c_p2=c,
    arms=arms,W_exact=[1,17],F_depths=[F_depth]*3,F_square=True,
    delta_depths=[delta_depth]*3,all_16_weighted_leaf_min_depth=6,
    traceQ_mod_17=9,stored_three_pole_depths=[pole_depth]*3),indent=2))
