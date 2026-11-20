#!/usr/bin/env python3
"""Independent continued-fraction exhaustion; stdin is the exact hex residue."""
from math import gcd, isqrt
import sys

M = 3**262188
a = int(sys.stdin.readline(), 16)
assert 0 < a < M
B = isqrt((M-1)//2)
n, d = a, M
b0, b1 = 1, 0
sign = 1
count = 0
positive = []
while d:
    quotient, next_remainder = divmod(n, d)
    b2 = quotient*b1+b0
    if b2 > B:
        break
    count += 1
    if sign == 1 and 0 < next_remainder <= B:
        positive.append((b2.bit_length(), next_remainder.bit_length(),
                         next_remainder < b2, 9*next_remainder > 8*b2,
                         isqrt(b2)**2 == b2, gcd(next_remainder, b2) == 1))
    n, d = d, next_remainder
    b0, b1 = b1, b2
    sign = -sign
assert count == 121065
assert positive == [(207778, 207779, False, True, False, True)]
assert (8*B//9+1).bit_length() == 207779
print("121065 convergents; one positive bounded remainder, H>b and b nonsquare; lower H bit length 207779")
