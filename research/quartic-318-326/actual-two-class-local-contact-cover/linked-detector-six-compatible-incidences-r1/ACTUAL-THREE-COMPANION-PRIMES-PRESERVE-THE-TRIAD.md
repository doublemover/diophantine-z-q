# One common retune supports three actual companion primes without losing the triad

This finite local certificate starts from the original fixed scalar
label J, the three literal scales, and the exact triad index and
numerator congruences 7a159177. It adds the following partner primes
in the SAME θ=−1 root class as the respective triad prime:

| original slot | retained triad p | new p | full primary / opposite R orders |
| --- | ---: | ---: | --- |
| 190 | 3162001 | 52056721 | 1626706 / 13014713 |
| 241 | 3641809 | 53279089 | 73988 / 2664341 |
| 292 | 4247281 | 95810641 | 4789765 / 1497281 |

All six designated contacts can be made simple in their assigned
row with one common t and one actual h. Only those designated
six primes are certified, not a full support. These are local
positive folded-pole exponents, not a rational PointPair.

## Finite character and exact literal scale arithmetic

The three new primes have original Gaussian rays

    (A,B_gauss) = (1065,7136), (3865,−6192), (−7671,−6080),

respectively. The checker uses exact trial primality, roots modulo
p², original half-point arithmetic and all proper prime-order
quotient tests for the two orders of R. It evaluates the literal
old s and Lucas labels modulo p times their respective full
residue order exactly as in the original triad certificate. The
four U charts are units at both arms; their products of −1/U are
the actual anchored scale data.

In particular the three scales modulo p² and all twelve distinct
nonzero scaled root residues are recorded at each new prime.
The new primes avoid the entire router B of f0016ec0. At an assigned
row, constrain T_j=c_j²t to −1+p modulo p² by prescribing
r/d=z/c_j where z²=−1+p mod p². This gives one exact simple contact
in its assigned row, and every factor in the other two scales is a
unit. All three additional numerator residues are compatible with
the three old numerator residues, by using the same square-contact
numerator CRT at all six distinct primes. It works for the symbolic
d=B^N, r prime to B and r arbitrarily large.

For each paired support, the new and old prime have identical
characters at (5,7,11,13,41). In particular both are nonresidues
at 7, reversing that entry and the other four indicated parity
obstructions factor by factor. But these pairs are **not complete**:
the first pair's product is a nonsquare modulo 23, and the
other two are nonsquares modulo 19. The saturation condition
0e75cbf1 implies each class needs another distinct additional
odd-support prime, on top of its already exhibited pair.
In particular all-six designated primes cannot be the complete
support for any corresponding saturated t. Matching selected
small characters never substitutes for the all-support condition.

## Exact shared h and local consequence

In the single CRT take h equal to the exact triad residue modulo
its exact index step. This retains all three of its primary full
entries, opposite full entries, exact p-adic depth-three conditions,
and the old stabilized scalar rows at J. Add at each new prime
h=0 mod its full primary order, 1 mod its full opposite order,
and h=p³ mod p^4. The replay checks all these congruences together,
not just individually compatible pairs. The new least positive
residue is also a certified actual real point of the original orbit:

    N(U([h]R)) in
    [−1495037357074303581,−1495037357074303580] / 2^64.

The interval is by outward 16384-bit dyadic point arithmetic and
its absolute value exceeds 1/100. The four original guards are
retained as nonzero by the exact old h modulo 5. The new h is not
equal to the old numeric representative, and the exact old scalar
value and invisible squareclass support are not asserted equal.

At every designated p the full oriented-source hypotheses of the
pointwise trace result 1beafde5 are met for that assigned row:
exact simple odd contact F, unit Δ and scale, actual primary
strong p³ and opposite entry at the same h. The exact sixteen
primary leaves and opposite parity give a unit rational trace,
hence v_p(b_j)=+1. The six local facts are each at the same h,t.
The other prime factors remain uncontrolled. The compact d=204
test is only a numerical CRT replay (and cannot give the full
PointPair by the 2399 denominator obstruction); it does not replace
the symbolic saturated construction. No other readiness or Lean
result is claimed.

    python3 -B check_actual_six_incidences.py | cmp - EXACT-SIX-INCIDENCES.json
    sha256sum -c SHA256SUMS

The exact modular and 16384-bit real verification is offline, pins
the prior JSON and arithmetic helpers, and does not run a discovery
search for candidate primes.
