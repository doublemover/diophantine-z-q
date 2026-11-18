"""Direct F_(p²) enumeration and the two exact squarefree twist abscissas."""
from itertools import product
from fractions import Fraction as F
from math import isqrt
import json
def count(p,d):
    field=list(product(range(p),repeat=2));assert all(x*x%p!=d for x in range(p))
    def m(x,y):return ((x[0]*y[0]+d*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    ys={}
    for x in field:
        v=m(x,x);ys[v]=ys.get(v,0)+1
    count1=1;count2=1
    for x in field:
        v=m(m(x,((x[0]-1)%p,x[1])),((x[0]+3)%p,x[1]));count2+=ys.get(v,0)
        if x[1]==0:count1+=sum((y*y%p,0)==v for y in range(p))
    return [count1,count2]
def sqroot(x):
    a,b=isqrt(x.numerator),isqrt(x.denominator)
    z=F(a,b);assert z*z==x;return z
def main():
    cc={p:count(p,d) for p,d in ((5,2),(7,3))}
    assert cc=={5:[8,32],7:[8,64]}
    B=17*F(204,1073)**2;V=B**2*(1-B/289);E=F(2014880256,4864365025);S=F(-1424848608,2768946245)
    Y=F(-2495222615232,5219463671825);Z=F(-115188947076336604087118173483290329088,4411321710125745115338446056112360723825)
    out=[]
    for n,x,y,N in [(E,B,Y,3026),(E*V,B*S**2,Z,1237634)]:
        u=sqroot(n/N);a=x/u**2;b=y/u**3
        assert b*b==a*(a-N)*(a+3*N)
        X=9*a+6*N;yy=27*b;assert X.denominator>1 and yy**2==X**3-351*N*N*X+1890*N**3
        out.append(dict(N=N,x=str(a),short_X=str(X)))
    assert out[0]['x']=='71825/16' and out[1]['x']=='5161217/4'
    return dict(counts_Fp_Fp2=cc,explicit_integral_twists=out)
if __name__=='__main__':print(json.dumps(main(),indent=2))
