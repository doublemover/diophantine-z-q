"""Exact finite dyadic models only; not Lean, topology or global duality."""
from fractions import Fraction
import json
counts = dict(restriction=0, compatibility=0, reconstruction=0, scalar_residue=0, annihilator=0)
for depth in range(9):
    modulus = 2**depth
    for coefficient in range(modulus):
        def character(k, x):
            return Fraction((coefficient*x) % (2**k), 2**k)
        for i in range(depth+1):
            for j in range(i,depth+1):
                for x in range(2**i):
                    assert character(j,x*2**(j-i)) == character(i,x)
                    counts['compatibility'] += 1
            for x in range(2**i):
                assert character(depth,x*2**(depth-i)) == character(i,x)
                counts['restriction'] += 1
                for a in (-3,0,1,6):
                    assert character(i,a*x) == ((a%(2**i))*character(i,x)) % 1
                    counts['scalar_residue'] += 1
            vanishes = all(character(i,x) == 0 for x in range(2**i))
            assert vanishes == (coefficient%(2**i) == 0)
            counts['annihilator'] += 1
        # A coherent family is recovered by its top coordinate; each lower
        # coordinate is the original subgroup restriction, not a new label.
        recovered = [character(depth,x) for x in range(modulus)]
        assert recovered == [Fraction((coefficient*x)%modulus,modulus) for x in range(modulus)]
        counts['reconstruction'] += modulus
print(json.dumps({'status':'PASS','scope':__doc__,'max_exponent':8,'checks':counts},indent=2))
