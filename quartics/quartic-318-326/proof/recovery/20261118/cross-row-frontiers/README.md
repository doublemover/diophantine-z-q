# Cross-row prime and compatible-order frontiers at two literal shared grids

**Do not combine these two parameters.** At the first we exhibit six distinct
compatible original prime values at eight indexed positions, spanning all
three rows. At the second, eleven of fifteen positions are prime (nine
distinct values), but no more than seven indexed positions can be
order-compatible, even if one discards other positions and freely reorients.
All maxima are specific to these two exact parameters and L=16,h₀=0. Neither
is full Values or any rational PointPair at a source-selected pole.

## Common model and arithmetic interpretation

Use the independently checked model-label tuple (−1,−1,−1,−1), not asserted
to be the affine labels of any original integer input. The previously proved
linked-row evaluation gives scales (1,3134049/4096,2825761/4096) from
fixedRoot(1)=1−7√2/4. In each row the exact five source slopes are
(0,−1/2,−1,1/2399,−32/407). With D=17294016221357051154 all
k_jl=−slope_l D²/scale_j² are integers, so D is a shared Clearing. This
is verified anew. At positive (u,w), the grid consists of u+k_jl w². All
three zero slopes give the same u, hence 13 distinct values in both
grids, whose indices are

    row 0: 0  1  2  3  4
    row 1: 0  5  6  7  8
    row 2: 0  9 10 11 12.

For a subset of prime values, Π denotes just their product, and an
orientation selects the minus sign at each such value, with the other
sign being plus. Write n± for the resulting exact signed orders of the
literal points (1+r,2r) on y²=x³−(3−r)²x, using both r²=2. The CRT
problem here is h=0 mod Π³ lcm(n−), h=1 mod lcm(n+), h=0 mod16.
The finite-field order interpretation agrees with good-reduction formal
quotient orders under the prior linked-row reduction argument. No local
Lean build, formal quotient execution or global guard comparison is claimed.

## Exact examples

* **COMPATIBLE-4030897.json.** Set
  u=10000000000000000002018987660553779409060163799522482685314202437075281,
  w=78196902643860. Nine positions are prime (seven distinct). Precisely six
  of their distinct values have t⁴=2: indices [0,2,4,5,8,10]. They are
  simultaneously compatible; one sign vector in the supplied root order
  is [0,1,1,0,0,0], and there are two compatible vectors on this subset.
  The seventh prime (index 3) fails H, so cannot be added. The resulting
  eight positions are row0:[0,2,4], row1:[0,1,4], row2:[0,2]. The file
  contains an explicit 2077-digit h, checked by exact integer remainders.
* **HIGH-PRIME-COUNT.json.** Set
  u=20873190861132578202270154506398615343414722637538936561, w=12939386460.
  Eleven positions are prime (nine distinct), seven distinct pass H, and
  all four remaining positions have proper factors. The maximum compatible
  signed subset is only five distinct values or seven indexed positions.
  One such subset [0,2,8,9,10] has signs [1,0,0,1,1] and the file gives
  its 1383-digit h. Discarding all dyadic failures is insufficient here:
  even the remaining seven distinct ray values cannot all fit.

Every prime in both examples is 1 mod816 and a quadratic nonresidue mod7;
a primitive-16th-root witness z⁸=−1 is checked individually. For H-passing
values, t⁴=2 is checked individually. For a failing value the fourth-power
Euler test is −1. Thus all selected positions meet these arithmetic ray
inputs. This is not an operator that produces prime samples for arbitrary
coefficients, a common h over all 15, or a proof of the full Gaussian
pattern. The numerical parameters are existence witnesses in a particular
shared-Clearing model.

## Self-contained proof certificates and maximality

Run python3 -B verify.py with the supplied sibling modules; compare stdout
to FINITE-REPLAY.json. The certificate data is generated offline; checking
does not need SymPy, FLINT, a prime distribution estimate, point-count
database, or an external theorem prover.

* Each primality certificate is recursive Pocklington, with F a fully
  prime-certified divisor of n−1, F²>n. For each prime q|F the provided
  witness a satisfies a^(n−1)=1 mod n and gcd(a^((n−1)/q)−1,n)=1.
  For every prime divisor p of n, ord_p(a) therefore contains the full
  q-part of n−1, so F divides p−1. Any such p exceeds √n; n is prime.
  The base case is 2. Every composite slot is covered instead by a literal
  proper factor. No probable-prime-only slot is counted.
* Each supplied positive multiple N of a signed order is independently
  verified by Jacobian double-and-add, not by assuming its CM origin.
  The included overlap-only algorithm factors only gcds among distinct
  signed keys or with the entire grid-prime product and L=16. It fully
  removes excess powers of these active primes while preserving a proven
  annihilator; private factors need not be factored. For every assignment,
  a prime that could affect a cross-side gcd or a test against Π or 16
  lies in this active support, and its final valuation is exact at every
  affected key. The support computed on all primes/keys contains that for
  every subset. Therefore the larger surviving multiples give precisely
  the same existence/obstruction as the true orders. Multiples can give
  a nonminimal h-period: only the explicit working h and existence are
  claimed. Even with arbitrary repeated choices for the three copies of
  index0 a compatible selection cannot put two copies in opposing
  orientations: each signed order is >1 (the affine R is never O), so
  the same nontrivial order would divide both LCMs. A selected index0
  may always occur three times consistently, with no change in feasibility.
* The checker directly enumerates skip/minus/plus at every distinct prime,
  respectively 3⁷ and 3⁹ assignments, on each chosen subset's own Π.
  Thus the maxima include possibilities omitting the shared root, and the
  weighted count adds exactly two when all its copies are present. This
  is stricter than testing just one pre-chosen sign vector. No factoring
  of the complete order-size bounds was needed.
