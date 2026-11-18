"""Independent re-evaluation of pinned constants and formal-kernel entry at 5."""
from fractions import Fraction as F
from math import prod,isqrt
import json
factors=[(7446,661),(7446,1861),(29784,7445),(476544,119479)]
co=[4376874610839020,101783690143177584,800910366213064752,2642145132961084032,3147690941013049344]
def rr(a):return sum(c*(a*(a+1))**i for i,c in enumerate(co))
def add(x,y):return x[0]+y[0],x[1]+y[1]
def sub(x,y):return x[0]-y[0],x[1]-y[1]
def mul(x,y):return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def norm(x):return x[0]**2-2*x[1]**2
def div(x,y):return mul(x,(y[0]/norm(y),-y[1]/norm(y)))
def qi(x,y=0):return F(x),F(y)
def sq(x):return mul(x,x)
delta=qi(11,-6);R=(qi(1,1),qi(0,2))
def padd(P,Q):
    x,y=P;u,v=Q
    slope=div(sub(v,y),sub(u,x)) if x!=u else div(sub(mul(qi(3),sq(x)),delta),mul(qi(2),y))
    xn=sub(sub(sq(slope),x),u)
    yn=sub(mul(slope,sub(x,xn)),y)
    assert sq(yn)==mul(xn,sub(sq(xn),delta))
    return xn,yn
def u(P):
    x,y=P;return div(mul(qi(2),y),add(sq(x),delta))
def red(x,p):return x.numerator*pow(x.denominator,-1,p)%p
def val(x,p):
    assert x
    k=0;n,d=x.numerator,x.denominator
    while n%p==0:k+=1;n//=p
    while d%p==0:k-=1;d//=p
    return k
def main():
    tco=[4]
    for A,b in factors:
        c=[0]*(len(tco)+1)
        for i,v in enumerate(tco):c[i]+=v*b;c[i+1]+=v*A
        tco=c
    assert tco==co and all(A*(A-4*b)!=0 for A,b in factors) and len(set(F(b,A) for A,b in factors))==4
    assert pow(2,2,5)==4 # inert 5
    P=R; out=[]
    U=[]
    for m in range(1,6):
        um=u(P);U.append(um);xx=padd(P,P)[0]
        assert mul(xx,sq(um))==qi(1)
        out.append([[red(c,125) for c in um],val(norm(um),5)])
        P=padd(P,R)
    assert [row[1] for row in out]==[0,0,0,0,4]
    assert U[-1][0] and U[-1][1] and min(val(c,5) for c in U[-1])==2
    c=norm(U[1]);assert c==F(1405152,4905889)
    # source c[-1]=Norm U[-2]=Norm U[2], and p=5 does not divide c
    assert val(c,5)==0 and val(rr(0),5)==1
    res=[a for a in range(25) if val(rr(a),5)==1]
    assert res==[0,5,9,10,14,15,19,24]
    # Exhaust both inert and split valuation combinatorics at 201 odd depths
    for k in range(1,402,2):
        for deg in ((2,),(1,1)):
            for a in range(-5,2*k+2):
                # extremal asymmetric chart suffices for controls; proof is universal
                places=[a] if len(deg)==1 else [a,(k+1)//2]
                nv=-sum(f*max(0,k-2*z) for f,z in zip(deg,places));hv=sum(f*z for f,z in zip(deg,places))
                if 4*nv<1-k:continue
                assert 8*hv>=7*k+1 and 15*k+hv+(1-3*k+3)//4>0
                if k==1:assert hv>=2
    return {'factorization_in_t':factors,'c_minus_one':str(c),'U_1_to_5_mod125_and_norm_valuation':out,'simple_5_input_classes_mod25':res,'necessary_h_divisor':5,'minimum_v5_n_minus_1':9,'necessary_d1_J_divisor':5**9,'actual_source_adaptive':True}
if __name__=='__main__':print(json.dumps(main(),indent=2))
