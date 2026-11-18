"""Literal binary-form and independent bad-prime residue controls; no CAS."""
from math import gcd,isqrt
from fractions import Fraction as F
import json
beta=17
def prime(n):return n>1 and all(n%a for a in range(2,isqrt(n)+1))
def chi(a,p):return {1:1,p-1:-1}[pow(a,(p-1)//2,p)]
def rem(a,N):return a.numerator*pow(a.denominator,-1,N)%N
def local_at_5(k):
 m=beta*k*k;a=25*beta-9/k**2;d=16*beta
 assert k.denominator%5==0 and k.numerator%5
 assert rem(a/25,5)
 # Choose nonzero actual 5-adic lifts by any smooth residue, allowing
 # residue zero in one coordinate; retain precision mod 25 at the unit norm level.
 pts=[(s,t) for s in range(1,26) for t in range(1,26)
      if (s*s-beta*t*t-rem(a/25,25))%25==0 and
         chi((25*s*s-d)*pow(beta,-1,5)%5,5)==1]
 assert pts
 return list(pts[0])
def run(th,n0,h0,d0,bit):
 assert n0*n0+th*h0*h0==beta*d0*d0 and gcd(n0,2*th*h0)==1
 assert (1 if pow(th,4,17)==1 else -1)==bit
 out=[];seen=set()
 for y in range(4):
  for x in sorted(range(-100,101),key=abs):
   if gcd(x,y)!=1:continue
   n=n0*x*x-2*th*h0*x*y-th*n0*y*y
   if n<=1 or n in seen or not prime(n):continue
   G=h0*x*x+2*n0*x*y-th*h0*y*y;D=d0*(x*x+th*y*y)
   if (2*beta*th*d0)%n==0:continue
   assert n*n+th*G*G==beta*D*D and gcd(n,beta*D)==1
   k=F(n,beta*D);m=beta*k*k
   assert (1-m)==beta*th*F(G,beta*D)**2 and chi(int(beta),n)==bit
   assert chi(n,17)==bit and (k.numerator%3)*(k.denominator%3)
   out.append(dict(x=x,y=y,n=n,k=str(k),split=bit==1,
       reduction5=local_at_5(k) if k.denominator%5==0 else None))
   seen.add(n)
   if len(out)>=4:return out
 raise ValueError('too few literal numerator primes')
def empty_residue(q):
 # With d=0 first enumerate (x1,x3), then (x2,T) on homogeneous cover.
 assert chi(beta,q)==-1
 v=[(a,c) for a in range(q) for c in range(q) if (a*a-beta*c*c)%q==0]
 w=[(b,t) for b in range(q) for t in range(q) if (beta*b*b-9*t*t)%q==0]
 assert v==w==[(0,0)];return len(v)*len(w)-1
if __name__=='__main__':
 ks=[run(409,1277,212,1085,1),run(457,439919,82276,439727,-1)]
 # A +bit example with TWO local failures shows one must test each prime.
 k=F(-869,18037);h=F(4*53,18037);assert 17*409*h*h==1-17*k*k and abs(k.numerator)==11*79
 print(json.dumps(dict(plus_bit=ks[0],minus_bit=ks[1],two_obstruction_plus_bit=dict(k=str(k),primitive_residue_counts={q:empty_residue(q) for q in [11,79]})),indent=2))
