#!/usr/bin/env python3
import json
from itertools import product

# Left differential d, right differential zero, middle
# (z,s) -> (d*z+c*s,0). Change the local lift by another
# left section and change the middle zero-splitting by a shear.
counts = {}
for d in (2,3,5,7,210):
    checked = 0
    for c, s, a, b, k in product((-17,1,23),range(-3,4),range(-5,6),
                               (3,8,-11),range(-9,10)):
        first = d*a+c*s
        other = d*b+c*s
        assert first-other == d*(a-b)
        targetlift = a+k*s
        targetc = c-d*k
        assert d*targetlift+targetc*s == first
        assert (first%d) == (other%d) == ((d*targetlift+targetc*s)%d)
        checked += 1
    counts[str(d)] = checked
print(json.dumps({"controls":counts,"total":sum(counts.values())},
                 indent=2,sort_keys=True))
