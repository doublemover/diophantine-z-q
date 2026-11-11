"""Exact finite coordinate/norm and numerical phase conventions, not a proof."""
from fractions import Fraction as F
from itertools import product
import cmath,json

def check():
    count=0
    for y in product((-2,-1,0,1,2),repeat=5):
        v=tuple(1 if a>=0 else -1 for a in y)
        dualnorm=sum(abs(a) for a in y)
        assert max(map(abs,y))<=dualnorm
        assert sum(a*b for a,b in zip(y,v))==dualnorm
        assert max(map(abs,v))==1
        count+=1
    for k in (318,326):
        x=(F(1,3),F(-2,5),F(3,7),F(-1,2),F(2,9));y=(2,-1,3,1,-2);beta=F(1,11)
        q=x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2
        dot=sum(a*b for a,b in zip(y,x))
        phase=cmath.exp(2j*cmath.pi*float(beta*q-dot))
        separated=cmath.exp(-2j*cmath.pi*float(dot))*cmath.exp(2j*cmath.pi*float(beta*q))
        assert abs(phase-separated)<1e-12
    return {'coordinate_norm_cases':count,'signed_phase_cases':2,'status':'PASS finite regression only'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
