#!/usr/bin/env python3
"""Exact-coefficient plus IEEE outward interval estimate for a specified positive fundamental companion twist.

Input is the little-endian integer stream produced by fixed48_theta_ntt.cpp.
The proof uses the Martin--Ono level 48 formula and Deligne, not a claim that
arbitrary external coef bytes are correct. Arithmetic only, no inferred trace.
"""
from fractions import Fraction as Q
from array import array
import sys,math,json

def atan_bounds(a,n):
    s=sum((Q((-1)**k,(2*k+1)*a**(2*k+1)) for k in range(n)),Q(0))
    t=s+Q((-1)**n,(2*n+1)*a**(2*n+1))
    return min(s,t),max(s,t)

def rational_exp_bounds(a,n=6):
    assert 0<a<1
    s=sum(((-a)**k/math.factorial(k) for k in range(n)),Q(0))
    t=s+(-a)**n/math.factorial(n)
    return min(s,t),max(s,t)

def qbounds(D):
    al,au=atan_bounds(5,20)
    bl,bu=atan_bounds(239,8)
    pi=(16*al-4*bu,16*au-4*bl)
    sl=Q(6928203230275509174,10**18)
    su=sl+Q(1,10**18)
    assert sl**2 < 48 < su**2
    u=rational_exp_bounds(2*pi[1]/(sl*D))[0]
    v=rational_exp_bounds(2*pi[0]/(su*D))[1]
    f=lambda r,d: math.nextafter(float(r),d)
    return f(u,-math.inf),f(v,math.inf)

def slow_coef(n):
    # Integer path independent of the NTT for a small prefix.
    y=0
    def sig(a): return 1 if a==0 else 2*(-1)**a
    for a in range(math.isqrt(n)+1):
      for b in range(math.isqrt(n//3)+1):
        for c in range(math.isqrt(n//4)+1):
            d=n-1-a*(a+1)-3*b*(b+1)-4*c*c
            if d>=0 and d%12==0 and (z:=math.isqrt(d//12))**2==d//12:
                y+=sig(c)*sig(z)
    return y

def main(fn,factors):
    assert (sys.float_info.radix,sys.float_info.mant_dig,sys.float_info.rounds)==(2,53,1)
    co=array("i")
    with open(fn,"rb") as f:
      co.frombytes(f.read())
    if sys.byteorder=="big":co.byteswap()
    assert all(co[i-1]==slow_coef(i) for i in range(1,201))
    D=math.prod(factors)
    assert D%12==1 and all(p>=5 and all(p%k for k in range(2,math.isqrt(p)+1)) for p in factors)
    assert len(set(factors))==len(factors)
    table=[]
    for p in factors:
        table.append([x if (x:=pow(a,(p-1)//2,p))!=p-1 else -1 for a in range(p)])
    chi=[math.prod(t[i%len(t)] for t in table) for i in range(D)]
    ql,qh=qbounds(D)
    down,up=lambda x:math.nextafter(x,-math.inf),lambda x:math.nextafter(x,math.inf)
    wl,wh=1.,1.
    lo,hi=0.,0.
    for n,a in enumerate(co,1):
        assert abs(a)<=2*n
        wl,wh=down(wl*ql),up(wh*qh)
        c=a*chi[n%D]
        if not c:continue
        r=float(c)/n
        rl,rh=down(r),up(r)
        if c<0: vl,vh=rl*wh,rh*wl
        else: vl,vh=rl*wl,rh*wh
        lo,hi=down(lo+down(vl)),up(hi+up(vh))
    # Deligne + d(n)<=2 sqrt(n) gives |a_n/n|<=2, including χ.
    tail=up(up(4*up(wh*qh))/down(1-qh))
    Llow=down(down(2*lo)-tail)
    Lhigh=up(up(2*hi)+tail)
    print(json.dumps({"fundamental_twist":D,"coefficient_count":len(co),
                    "q_bounds":[ql,qh],"positive_tail_abs_bound":tail,
                    "central_value_interval":[Llow,Lhigh],
                    "interval_excludes_zero":Llow>0 or Lhigh<0},indent=2))

if __name__=="__main__":
    main(sys.argv[1],list(map(int,sys.argv[2:])))
