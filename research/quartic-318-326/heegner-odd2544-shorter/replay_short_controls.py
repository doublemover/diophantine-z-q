#!/usr/bin/env python3
"""Rerun the bounded actual coefficient countercontrols and reference."""
from math import isqrt
import json
import sys
from pathlib import Path
from check_negative_small import OLD_REPS,src
from recalibrate_short_auxiliaries import coeff

book=json.loads(src.SOURCE.read_text())
assert src.hashlib.sha256(src.SOURCE.read_bytes()).hexdigest().startswith('aa650e28')
root=Path(__file__).resolve().parent

def row(m,d):
    assert m==455 and d%24==11 and all(d%p for p in range(2,isqrt(d)+1))
    assert src.leg(-m,d)==1 and src.leg(d,53)==-1
    a=coeff(book,-d,37)
    assert a==coeff(book,-d,37,OLD_REPS)
    b=coeff(book,m*d,-35)
    return a,b,10*(a['coefficient_mod13']*b['coefficient_mod13'])**2%13

def main():
    p=(5,7,13,17,19,37,53)
    rs=[]
    for d in (1931,2579):
        a,b,t=row(455,d)
        rs.append(dict(d=d,m=455,legendre=[src.leg(d,q) for q in p],legendre_minus_m_at_d=1,
                       residue_d_mod24=d%24,negative=a,positive=b,square_mod13=t))
    assert rs[0]['legendre']==rs[1]['legendre'] and [r['square_mod13'] for r in rs]==[0,1]
    ans=dict(legendre_places=p,rows=rs)
    assert json.loads((root/'SHORT-MATCHED-LOCAL-COUNTERCONTROL.json').read_text())==json.loads(json.dumps(ans))
    print(json.dumps(ans,indent=2,sort_keys=True))
if __name__=="__main__":main()
