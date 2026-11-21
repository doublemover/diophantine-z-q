# An explicit principal element isolating the actual mirror test prime at 53

Use the degree-168 mirror F^c and the same degree-13
test prime of the
[actual strict ordinary class certificate](../actual-one-I-strict-ordinary-class-r1/EXACT-STRICT-SELMER-ORDINARY-CLASS-CERTIFICATE.md).
The relative integral line generator is B, and the
literal mirror generator is Z=sum_a sigma_a(W) ζ13^a.
Let m_B be the exact degree-13 factor of the line
polynomial modulo 53 from the previous replay.

The finite field at the chosen nonfixed branch has
B-residues which span the whole F_(53^13). Solving
the exact 13×13 coordinate system gives Z≈G(B) on
that branch, where the centered integral lift is

    G(B)=26B^12−5B^11−3B^10−22B^9+22B^8+20B^7
         −9B^6+9B^5−10B^4+20B^3−9B²+16B+18.

Across the 12 distinct relative primes over this same
degree-13 line prime, the values of Z obtained from
all cyclotomic dilations are distinct modulo 53.
The other line factor has B=23, and the separately
calculated 12 fixed-point mirror values are all
different from G(23). This covers all 24 primes
over 53 (twelve of degree 13 and twelve of degree 1).
Therefore the actual ordinary test ideal is exactly

    q_53 = (53, m_B(B), Z−G(B)) O_(F^c).

No index-one claim on Z or the full displayed order
is needed: the prime 53 is unramified in F^c and
the residue tests isolate one prime among all its factors.

In fact the simple global integral element gamma=Z−G(B)
is a unit at every other prime above 53. At q_53
the exact unramified lift through 53² makes its
normalized valuation one. The replay lifts first the
true x division polynomial root, then the actual W
quadratic root in the same branch, and lifts ζ from
16 by its cyclotomic equation. It computes all twelve
W([a]P) by affine addition with denominators that
are units on this branch. The final expression gamma
is divisible by 53 but not by 53²; its exact
gamma/53 residue vector is archived. No adjustment
or search over extra scalar shifts was needed.

This is an exact principalization of the **53-part**
of q_53: div(gamma) at 53 is exactly q_53. Its residue
class in the global ideal class group is of course
zero; the divisor outside 53 is not calculated in
this packet. In particular this does not claim
absolute principality of q_53, its reduction to a
practical factor base, or any class-rank bound.

    sha256sum -c SHA256SUMS
    python3 -B check_actual_q53_principal_localization.py | cmp - EXACT-ORDINARY-Q53-IDEAL-AND-PRINCIPAL-CHART.json
