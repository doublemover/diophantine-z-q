"""Pure integer replay for the five-prime pole's NEGATIVE torsion anchor."""
from itertools import product
from math import prod, isqrt

B=(17,409,2857,3673,6121,6529); H=(131,577,1367,9133)
b,h,D=prod(B),prod(H),20491203655
N=b*h
def vpunit(x,p):
    assert x
    v=0
    while x%p==0: v+=1; x//=p
    return v,x
def leg(x,p):
    x%=p
    assert x
    return 1 if pow(x,(p-1)//2,p)==1 else -1
def cl(x,p):
    if not p: return (x>0)
    v,u=vpunit(x,p)
    return (v%2,u%8 if p==2 else leg(u,p))
def hilb(a,c,p):
    if not p: return -1 if max(a,c)<0 else 1
    j,u=vpunit(a,p);k,v=vpunit(c,p)
    if p==2: return (-1)**((((u-1)//2)*((v-1)//2)+j*((v*v-1)//8)+k*((u*u-1)//8))%2)
    return (-1)**((j*k*(p-1)//2)%2)*leg(u,p)**(k%2)*leg(v,p)**(j%2)
def run():
    assert all(all(p%i for i in range(2,isqrt(p)+1)) for p in (2,3)+B+H)
    assert b==2915898793659694097 and h==943689409057 and D**2-144*b==h
    assert (-1001545)**2-3*140716**2==h
    assert 302690087790674**2-3*b*3819**2==h*311373085**2
    assert h%24==1 and all(leg(h,p)==1 for p in B)
    assert all(leg(3,p)==leg(b,p)==1 for p in H)
    survive=[]
    for bits in product((0,1),repeat=8):
        d=3*17*prod(p**bit for p,bit in zip((2,)+B[1:]+(577,9133),bits))
        if cl(d,3)!=cl(3*b*h,3):continue
        if any(cl(d,p) not in ({cl(3*b*h,p)}|({cl(-3*h,p)} if leg(-3*h,p)==1 else set())) for p in B):continue
        if any(cl(d,p) not in ({cl(1,p)}|({cl(-h,p)} if leg(-3*b,p)==1 else set())) for p in H):continue
        survive.append(d)
    assert survive==[3*b]
    # Kummer triples for O, T1, T3; T3 at x=-3N, other finite root 9N.
    for p in [0,2,3]+list(B)+list(H):
        delta=((-27*N*N,-9*N,3*N) if p==0 else
               (-3*N,-12*N,36*N*N) if p in (2,3,17) else (1,1,1))
        assert [cl(x,p) for x in delta]==[cl(x,p) for x in (-51,-51,1)]
    signs={}
    for p,k,t,expected in [(2,12,145,[(2,3),(0,1)]),(3,8,2528,[(0,2),(0,1)]),(17,3,2310,[(1,8),(0,15)])]:
        assert (t*t-h)%p**k==0
        vals=(2*D*t-2*h,-(2003090+422148)*t-h)
        uu=[(j,u%(8 if p==2 else p)) for j,u in (vpunit(x,p) for x in vals)]
        assert uu==expected
        # Hensel root agrees mod p^(k-v_p(2t)); enough precision for both unit residues.
        assert k-vpunit(2*t,p)[0]>=max(j+(3 if p==2 else 1) for j,_ in uu)
        signs[p]=prod(hilb(x,-51,p) for x in vals)
    assert D>0 and D**2>h   # L1 positive at real r=+sqrt(h), L2 negative
    assert signs=={2:1,3:-1,17:-1}
    return dict(candidate_count=256,surviving_d=survive[0],local_signs={**signs,'infinity':-1},global_sign=-1)
if __name__=='__main__':print(run())
