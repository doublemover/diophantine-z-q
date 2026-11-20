#!/usr/bin/env python3
"""Fixed small CRT scalar alone; does not expand θ or the auxiliary field."""
import json

B=(5,11,17,163,661,733,1489,1861)
A=500907037962860804880

def leg(n,p):
    y=pow(n,(p-1)//2,p)
    assert y in (0,1,p-1)
    return -1 if y==p-1 else y

def possible(t):
    return (t%12==0 and all(leg(1-t*t,p)==1 for p in B)
            and leg(17*t*t-1,53)==-1)

def main():
    t=21060
    d53=(1-A*pow(17*(1+A)**2,-1,53))%53
    assert d53==17 and leg(d53,53)==1
    assert possible(t) and not any(possible(s) for s in range(12,t,12))
    print(json.dumps(dict(offset=t,beta_primes=B,
        minus_M_residues_at_beta=[(1-t*t)%p for p in B],
        dict_Delta_at_53=d53,M_mod_53=(d53*t*t-1)%53,
        norm_identity="Norm((1+sqrt(-M))/t)=delta",
        actual_theta_factored=False, actual_positive_coefficient_read=False),
        indent=2,sort_keys=True))

if __name__=="__main__":
    main()
