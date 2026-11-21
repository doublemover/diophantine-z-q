# Three complementary partner pairs retain all six known contacts

Keep the exact original scalar J, its four literal Lucas labels, and
the three fixed detector scales. Keep every h and numerator congruence
of the independently checked six-contact certificate, not its
particular numerical h. This certificate adds two prime incidences to
each of the same three θ=−1 root classes:

| Slot | Two previously retained primes | Two new primes | New full primary / opposite orders |
| --- | --- | --- | --- |
| 190 | 3162001, 52056721 | 17590513, 1476960817 | 1098980 / 4399337; 46156450 / 369228809 |
| 241 | 3641809, 53279089 | 4818481, 344853841 | 80295 / 75301; 2155130 / 86221721 |
| 292 | 4247281, 95810641 | 16688017, 583021393 | 347772 / 834149; 18220514 / 3238813 |

The two-prime choice is useful because every old Gaussian-ray prime is
a nonresidue at 7. A **single** third prime preserving the already
balanced 7 row would instead have (p/7)=+1. At a split θ=−1 contact
p≡1 mod8, so (7/p)=+1. Then the two actual arm curves are isomorphic
over F_p: if d=3−rho and d'=3+rho with rho²=2, use u=d/sqrt(7),
so u²=d/d' and (x,y)↦(u²x,u³y) maps E_{d'} to E_d. The weak
primary and opposite orders must then be disjoint inside a single
fixed finite group, a constraint the two old-ray primes avoid.
Precisely, if the shared group has size G, the primary
ord(2R) divides G/4 by full rational two-torsion; the opposite
order modulo {O,T0} must be odd for even h and divides G/2, so
also divides G/4. Coprimality implies their product divides G/4.
This is a necessary filter only, not a no-go theorem for one prime.

For the new complementary pair, both primes instead lie in the old
Gaussian ray so their 7 signs cancel. Search pairs by XOR of their
finite old small-prime signatures and retain only exact full-order
CRT choices. The offline certificate checks the selected primes,
not the discovery search or minimality of the roster.

## Exact shared t and h

At each new prime trial primality, p² square roots, independent
proper-order tests inside both literal arms, and a nonzero first
formal return modulo p² verify the exact full orders and formal
depth one. Modular Lucas values at p times each arm order recover all
four actual chart units, their products of −1/U, and the three scales.
The twelve nonzero roots are distinct mod p and all scales, roots and
root-minus-one normalizers required by the router are units. Hence
each p avoids the entire saturation integer B.

Choose r/d=z/c_j mod p² where z²=−1+p; thus T_j+1=p mod p², at its
designated scale, and every contact factor in the other two rows is
a unit at p. Use ordinary CRT for all twelve numerator conditions
and primitive r mod B, for the symbolic d=B^N and arbitrarily large
r. The numerical denominator d=204 in the checker is a local replay
only and cannot provide a complete witness (the separate 2399 theorem).

At both old and new primes keep the same three exact conditions:
h=0 mod the full primary order, h=p³ mod p^4, h=1 mod the full
opposite order. The resulting common h residue and modulus extend
the *entire* preceding six-prime progression, including the
stabilized old scalar rows at the same J and old modulo 5 guards.
The least passing positive index has the following rigorous outward
real control for the actual original chart, with absolute value
greater than 1/100:

    N(U([h]R)) in [904477195540417060,904477195540417061] / 2^64 (32768-bit directed dyadics).

Together these satisfy the existing pointwise sixteen-leaf and
trace-unit proof at each of the twelve named primes. In particular
the literal stored coefficient in each designated slot has
v_p(b_j)=+1 at its listed prime, all on the shared h,t. Other primes
are not controlled. We do not identify the old scalar value with the
one at the new h, nor assume the two remaining pole certificates.

## Exact sign scope, which is NOT full support

Each of the three nominated four-prime products satisfies the
necessary squareclass character test at **every prime up to 47**,
including 2 (all factors p≡1 mod8). The first remaining failures
are respectively 59,59,53. Those fixed primes of B force at least
one more distinct odd-support prime in each of the three already
hit classes. The separate cross-symbol theorem from the original
triad forces nonempty support in all nine other nonzero classes.
Consequently any completion of this same saturated square branch
with all twelve named contact congruences needs at least **24**
odd-support primes (12 known + 3 still forced in their own classes
+ 9 elsewhere), not an actual complete roster. If it uses only
primes in the old 7-nonsquare Gaussian ray, every class needs even
cardinality, so the lower bound becomes 36 (three classes with at
least six each, nine with at least two each). That restricted class
bound does not exclude a general completion with other rays.

Run:
    python3 -B check_actual_twelve_incidences.py | cmp - EXACT-TWELVE-INCIDENCES.json
    sha256sum -c SHA256SUMS

This is an exact author finite replay, not a Lean result, full support
certificate, square pole denominator theorem, or rational PointPair.
