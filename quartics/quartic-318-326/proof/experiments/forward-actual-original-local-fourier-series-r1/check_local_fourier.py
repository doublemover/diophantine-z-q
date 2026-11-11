"""Finite independent normalization checks; not a Lean proof or global count."""
import cmath,itertools,json
from fractions import Fraction

def check():
    cases=[]
    for k in (318,326):
        for q in range(1,8):
            hist=[0]*q
            for a,b,c,d,w in itertools.product(range(q),repeat=5):
                hist[(a*a+b*b-c*c-d*d-k*w*w)%q]+=1
            complete=sum(hist[r]*sum(cmath.exp(2j*cmath.pi*a*r/q) for a in range(q)) for r in range(q))
            assert abs(complete-q*hist[0])<1e-7
            assert abs(complete/q**5-float(Fraction(hist[0],q**4)))<1e-7
            cases.append({'k':k,'q':q,'count':hist[0],'normalized':str(Fraction(hist[0],q**4))})
    for p in (3,5,53,163):
        r=Fraction(1,p**3); S=(1-Fraction(1,p**4))/(1-r)
        b=[S+(1-S)*r**(n//2) for n in range(25)]
        layers=[b[0]]+[b[n]-b[n-1] for n in range(1,len(b))]
        assert all(x>=0 for x in layers)
        assert all(sum(layers[:n+1])==b[n] for n in range(len(b)))
    return {'finite_complete_frequency_checks':cases,'parity_telescoping_cases':4,'status':'PASS finite checks only'}
if __name__=='__main__': print(json.dumps(check(),indent=2))
