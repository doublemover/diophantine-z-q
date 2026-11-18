"""One real-quadratic half-trace test on an exact prepared (not original indexed) pole."""
import sys,random,json,hashlib
from pathlib import Path
from math import gcd
from flint import fmpz
base=Path(__file__).resolve().parent.parent/'heegner'
sys.path.insert(0,str(base))
from fast_trace import ctx,point_at,add,double,reduced,oriented
def sum_points(P,seed):
    random.Random(seed).shuffle(P)
    while len(P)>1:P=[add(P[i],P[i+1]) if i+1<len(P) else P[i] for i in range(0,len(P),2)]
    return P[0]
def cls_sign(F,d,theta):
    a,b,c=F
    for h in range(1,64):
        for y in range(h+1):
            for x in (-h,h) if y!=h else range(-h,h+1):
                m=a*x*x+b*x*y+c*y*y
                if gcd(x,y)==gcd(m,2*d)==1:return int(fmpz(theta).jacobi(fmpz(m)))
    raise ValueError("no represented coprime norm")
def cert(d,theta):
    n=d//theta;D=-d
    assert d==n*theta and d%24==n%24==23 and theta%24==1 and theta>1
    assert d==800207 and theta==457
    path=base/'fast_trace.py'
    assert hashlib.sha256(path.read_bytes()).hexdigest()=='ac640653fe425c8ac7e04e8783c5b2ce2f326f8514fbfe8c874e7eb128ee5a8e'
    ctx.prec=1536; zz=reduced(d); rr=min(i for i in range(96) if (i*i+d)%192==0)
    meta=dict(forms=[oriented(z,rr) for z in zz],h=len(zz));assert fmpz(17).is_prime() and fmpz(103).is_prime() and fmpz(457).is_prime() and 17*103*457==d
    classes={i:[] for i in (-1,1)}
    for F in meta['forms']:
        s=cls_sign(F,d,theta);classes[s].append(point_at(d,F))
    assert len(classes[1])==len(classes[-1])==meta['h']//2
    A=sum_points(classes[1],1);B=sum_points(classes[-1],2)
    xplus=D*double(A)[0];xminus=D*double(B)[0]
    assert xplus.imag.contains(0) and xminus.imag.contains(0)
    assert not (xplus-xminus).contains(0)
    return dict(n=n,theta=theta,d=d,counts=[len(classes[1]),len(classes[-1])],bits=ctx.prec,x_twice_plus=str(xplus),x_twice_minus=str(xminus),difference=str(xplus-xminus),rigorous_disjoint=True)
if __name__=='__main__':print(json.dumps(cert(800207,457),indent=2))
