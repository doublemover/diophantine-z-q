#!/usr/bin/env python3
"""Exact Fraction arithmetic for rational approximation/separation; not Lean or minor decay."""
from fractions import Fraction as F
from math import gcd,floor
from pathlib import Path
import json

def run():
 counts=dict(centered_representatives=0,scaled_error=0,all_integer_translates=0,short_block_pairs=0,negative_controls=0)
 for q in range(1,16):
  for a in range(-q,q+1):
   if gcd(q,a)!=1:continue
   for error in (F(-1),F(-1,2),F(0),F(1,2),F(1)):
    t=F(a,q)+error/(q*q)
    for c in range(-q//2,q//2+1):
     if abs(c)>F(q,2):continue
     assert abs(c)*abs(q*t-a)<=F(1,2)
     counts['scaled_error']+=1
     x=c*t;m=floor(x+F(1,2))
     assert abs(x-m)<=F(1,2)
     counts['centered_representatives']+=1
     if c%q:
      for j in range(m-3,m+4):
       assert c*a-j*q!=0
       assert F(1,2*q)<=abs(c*t-j)
       counts['all_integer_translates']+=1
    for lo in (-3,0,7):
     hi=lo+q//2
     for c in range(lo,hi+1):
      for d in range(lo,hi+1):
       if c==d:continue
       assert (c-d)%q!=0
       x=(c-d)*t;m=floor(x+F(1,2))
       assert F(1,2*q)<=abs(c*t-d*t-m)
       counts['short_block_pairs']+=1
 # Genuine necessity controls: coprimality, nonmultiple condition,
 # block range, approximation quality, and nearest-integer centering.
 assert F(1,8)>abs(2*F(2,4)-1) and gcd(4,2)!=1
 assert F(1,4)>abs(2*F(1,2)-1) and 2%2==0
 assert abs(F(1,4)-F(1,3))<=F(1,9) and 4%3 and F(1,6)>abs(4*F(1,4)-1)
 assert F(1,6)>abs(F(0)) and abs(F(0)-F(1,3))>F(1,9)
 assert abs(F(3,4)-floor(F(3,4)))>F(1,2)
 counts['negative_controls']=5
 result={'status':'PASS','scope':__doc__,'checks':counts}
 Path(__file__).with_name('RATIONAL-SPACING-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
