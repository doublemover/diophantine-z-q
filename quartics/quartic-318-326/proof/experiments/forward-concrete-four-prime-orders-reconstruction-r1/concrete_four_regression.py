"""Exact bounded certificate discovery; no Lean or distribution inference."""
from pathlib import Path
import json,math
from sympy import nthroot_mod
ROOT=Path(__file__).resolve().parent
D=int(json.loads((ROOT/'r54-global-doubles-recomputed.json').read_text())['16']['denominator'])
def prime(n):
 if n<2:return False
 if n%2==0:return n==2
 return all(n%d for d in range(3,math.isqrt(n)+1,2))
def point_count(p,r):
 squares={y*y%p for y in range(1,p)}
 coeff=(3-r)**2%p
 return 1+sum(1 if (v:=(x*x*x-coeff*x)%p)==0 else (2 if v in squares else 0) for x in range(p))
rows=[];screen=0
for k in range(-12,13):
 for l in range(-12,13):
  a,b=57+112*k,80+112*l;p=a*a+b*b
  lo,hi=(a-1)**2+b*b,(a+1)**2+b*b
  assert lo%64==0 and hi%4==0
  m,n=lo//64,hi//4
  if not (prime(p) and prime(m) and prime(n)):continue
  screen+=1
  if pow(2,(p-1)//4,p)!=1:continue
  t=int(nthroot_mod(2,4,p));z=int(nthroot_mod(p-1,8,p));r=t*t%p
  assert pow(t,4,p)==2 and pow(z,8,p)==p-1
  assert (a%16,b%16,a%7,b%7)==(9,0,1,3)
  assert D%p!=0 and math.gcd(n,16*m)==1
  counts=[point_count(p,r),point_count(p,(-r)%p)]
  assert sorted(counts)==sorted([lo,hi])
  rows.append(dict(p=p,a=a,b=b,minus_count=lo,plus_count=hi,minus_odd_prime=m,plus_prime=n,fourth_root_two=t,eighth_root_negative_one=z,denominator16_residue=D%p,residue_sqrt_two=r,experimental_point_counts=counts))
rows.sort(key=lambda row:row['p'])
minus=math.lcm(*(16*r['minus_odd_prime'] for r in rows));plus=math.prod(r['plus_prime'] for r in rows)
assert math.gcd(minus,plus)==1
result={'search_box':{'k':[-12,12],'l':[-12,12],'a':'57+112*k','b':'80+112*l'},'tested_pairs':625,'three_prime_candidates':screen,'successful_explicit_root_certificates':len(rows),'primality_method':'Exact exhaustive odd trial division through integer square root','rows':rows,'cross_upper_lcm_gcd':math.gcd(minus,plus),'minus_upper_lcm':minus,'plus_lcm':plus,'scope':'Discovery and finite arithmetic validation only. Existing generic native theorems would turn each row into actual plus order n, opposite order dividing16m and divisible by m, and this packet contains dedicated theorem declarations for all four rows, still pending independent review and kernel replay. These four independent primes are NOT values of the original fifteen-position common-pair pattern. No simultaneous tuple, continuity compatibility, normalized mass or density assertion.'}
print(json.dumps(result,indent=2))
