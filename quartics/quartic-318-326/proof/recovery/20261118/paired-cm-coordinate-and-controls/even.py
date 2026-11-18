"""Certified Mellin central values for the normalized level-48 newform's even twists, k≡1 mod24."""
from pathlib import Path
import sys,json,hashlib
from math import prod
from flint import arb,ctx,fmpz
base=Path(__file__).resolve().parent.parent/'analytic'
sys.path.insert(0,str(base))
from derivative import euler
def certify(k,T):
    assert k>1 and k%24==1
    fac=fmpz(k).factor()
    assert prod(int(p) for p,e in fac)==k and all(e==1 and p.is_prime() for p,e in fac)
    ctx.prec=96; K=(T+1)//2
    a=euler(1,K).mul_low(euler(2,K),K);a=a.mul_low(euler(3,K),K).mul_low(euler(6,K),K)
    n=fmpz(-k);c=arb.pi()/(2*arb(3).sqrt()*k)
    P=arb(0)
    for j in range(K):
        if a[j]:
            m=2*j+1;h=n.jacobi(fmpz(m))
            if h:P+=2*int(a[j])*int(h)*(-c*m).exp()/m
    err=4*(-c*(T+1)).exp()/(-(-c).expm1());L=P+(-err).union(err)
    return dict(k=k,T=T,primes=[int(p) for p,e in fac],L_lower=str(L.lower()),L_upper=str(L.upper()),positive=bool(L>0))
if __name__=='__main__':print(json.dumps([certify(k,18*k) for k in (73,457,73*409)],indent=2))
