# Second formal jets give a certified dual-plane search

Use the fixed actual one-I marked ξ-lift, after the exact reduction
in the sibling [CFS packet](../actual-one-I-third-cover-reduced-r1/EXACT-REDUCED-MARKED-POINT-SEARCH.md).
We do not search Cartesian coordinate boxes. Rather, a finite collection
of rational planes is shown to contain every sufficiently small rational
point, and we test each complete plane section, at **all** heights.
The exact computation at prime 59 certifies 3,776 such sections in
8.3 seconds, needing only 15 exact characteristic-zero resultant
computations. They contain no rational points. Their certified coverage
includes every primitive reduced vector of sup height at most **97039**.

This is a bounded exclusion. Neither a global point, an effective
global height bound, a base rank nor any companion assertion follows.

## The actual p-adic neighborhoods

Fix a good odd prime p, exponent k≥1 and N=p^k. At each smooth
projective point of the curve mod p choose its last nonzero coordinate
as pivot one, and two other coordinates j,l at which the determinant
of the two-quadric derivatives is a unit. The remaining coordinate t
is a free local parameter. In each class modulo N, fix the parameter
r modulo N. Hensel's lemma gives every solution with that residue
uniquely in the two dependent coordinates for each t=r+N s.

Write the two polynomials Q as homogeneous quadrics in (x0,x1,x2,x3),
and polar matrix DQ for their two gradient rows. Choose v0, with pivot
one and parameter exactly r, so Q(v0)=0 mod N³. Choose v1 with pivot
zero and parameter one, and v2 with both those coordinates zero, from

```
DQ(v0) v1        = 0          mod N²,
DQ(v0) v2+Q(v1)  = 0          mod N.
```

The same invertible j,l minor solves both systems. The exact quadratic
expansion then gives, for every s, a solution modulo N³ with parameter
r+N s:

```
v0 + N s v1 + N² s² v2.
```

The prescribed two coordinates coincide with the Hensel lifts by
uniqueness. Hence the primitive integer points x in this neighborhood,
whether or not of small height, lie in the additive lattice L generated
by v0, N v1, N² v2 and N³ Z⁴. Here we multiply the normalized
projective solution by the actual integer pivot x_i, which is a unit
at p, and compare modulo N³. No approximation over R is used.

The image of L modulo N³ has size at most N³·N²·N=N⁶, so its
index in Z⁴ is at least N⁶ (not N⁵ as for the first tangent alone).
The script constructs the dual integrally: if written as λ/N³,
its congruences are λ·v2=0 mod N, λ·v1=0 mod N², λ·v0=0 mod N³.
The first is a single constraint on λ_j,λ_l of index N/g, with
g=gcd(N,v2_j,v2_l); parameter coordinate and pivot then contribute
indices N²,N³ to the integer numerator lattice. The exact
primal index is therefore N⁶g. The actual computation at 59 has
g=1 for all 3,776 neighborhoods. The standard
[Elkies/Heath-Brown search described by Fisher §6.2](https://www.dpmms.cam.ac.uk/~taf1000/papers/sixandtwelve.pdf)
motivates this localization; the second-jet constraints above are
checked directly rather than asserted from a floating cutoff.

## Dual planes and exact cost

For a nonzero vector w in L*, the pairing w·x is integral. If
B‖w‖₁<1 then **every** vector x in L of sup height ≤B has w·x=0.
For a given integer numerator λ of w, the exact coverage is
floor((N³−1)/‖λ‖₁). Dividing out the common factor of λ then
gives the primitive integer normal of the same rational plane.

Use lattice reduction at δ=3/4 in dimension 4. Gram–Schmidt gives
‖w1‖₂ ≤ 2^(3/4) det(L*)^(1/4) for the first reduced dual vector,
since each consecutive squared Gram–Schmidt length has ratio at
least 1/2. Since ‖w1‖₁≤2‖w1‖₂ and det(L*)≤N^(−6), it is
sufficient that N⁶>128 B⁴. In an exact run we use the stronger
individual height caps, not just this uniform estimate. The
transformed integer dual basis and selected dot products are
verified exactly in each bin, independently of that estimate.

On a fixed good prime, the number of original residue points is fixed.
The number of depth-k neighborhoods is one factor p^(k−1) more by
the free parameter. Thus the least p-power N with N⁶>128 B⁴ yields
O(B^(2/3)) neighborhoods. Each bin is finite-dimensional exact
Hensel arithmetic, integral LLL in constant dimension, and solving a
constant-degree rational system; entry lengths are O(log B) on the
fixed curve (rational polynomial factorization is polynomial in bit
length). This gives a rigorous O(B^(2/3) polylog B) bit-cost upper
bound for the complete search, not a heuristic output argument
based on determinant alone. In comparison, the first-jet method
is based on the depth-N² tangent lattice of index N⁵ and gives
exponent 4/5 by the same proof.

To test a plane, reduce its primitive normal at independently chosen
small good primes and check incidence with the complete projective
curve there. If no incidence is found at one prime, the plane section
has no rational point, of any height. For the remaining sections
substitute a rational plane chart into the two quadrics. The
curve is a nondegenerate geometrically integral complete
intersection of degree four, so no plane contains it and the
section is finite. In the affine chart the resultant is nonzero;
take every rational root and the full gcd of the two univariate
fibers. The line at infinity and its remaining point are checked
separately. Any result (even above B) is accepted only after a
literal equality check in both original reduced quadrics and the
plane equation. It would give a nontorsion point by the exact
mark back-map in the CFS packet.

## Actual output and checks

- At 59, k=2, **second jet**: 64 residue points, 3,776 neighborhoods
  and different planes, actual uniform coverage 97039, 15
  characteristic-zero sections after the exact modular screen,
  and no point on the entire union.
- First-jet controls have the same geometric curve. At 59, k=2
  there are 3,756 different planes and uniform coverage 13185.
  At 101, k=2 there are 8,484 neighborhoods, 8,473 different planes
  and coverage 49933. Neither union has a rational point; the
  latter needs only nine resultants after its independent screens.

The residue enumerator eliminates one coordinate quadratically
in O(p²); on 59 and 101 the script checks it against all projective
representatives as a control. Both checkers and the reduced coefficient
JSON in the sibling CFS packet are pinned by digest from the
actual former stage. No new external package is required apart
from the same SymPy 1.14 used there.

```sh
sha256sum -c SHA256SUMS
python3 -B check_dual_planes.py --jet 2 --bound 60000 | cmp - EXACT-59-DEEP2-SECOND-JET.json
python3 -B check_dual_planes.py | cmp - EXACT-59-DEEP2-PLANES.json
python3 -B check_dual_planes.py --p 101 --bound 30000 | cmp - EXACT-101-DEEP2-PLANES.json
```

A distinct possible next gain uses the eight-dimensional degree-two
coordinate ring of this (2,2) complete intersection. After choosing
eight monomial representatives modulo the two old equations, one
could retain the formal coefficients of all eight values up to order
six modulo N⁷. The analogous evaluation lattice has index at least
N^(1+2+···+7)=N²⁸. A nonzero dual relation gives a *new* quadric, not
in the ideal generated by the old pencil, and its actual rational
intersection with the curve has degree eight. The box bound then
suggests the rigorously targetable exponent 4/7 for rational point
search, once the finite dimension-eight jet and rational resulting
intersection are implemented. No such degree-eight computation is
part of this packet.
