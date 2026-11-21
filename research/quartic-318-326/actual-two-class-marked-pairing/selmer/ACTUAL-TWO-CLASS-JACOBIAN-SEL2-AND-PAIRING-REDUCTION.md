# The actual two-factor Jacobian already has three pure Selmer directions

Work with either valid choice of the two new primes produced in the
reviewed two-class local theorem (7a597052). This is uniform over
those choices, not a conjectural rank calculation or a computed
Sha class. Write

    a = sigma_a = 415721 q_a,   b = sigma_b = 9807649 q_b,
    D = ab,
    s = s_a = −32/(407 c_1²),   t = s_b = 1/(2399 c_2²),
    E_D: y² = x(x−D s)(x−D t).

The supports of a,b are disjoint and outside B. They are positive
local squares at all primes dividing B. Each q_i is 1 mod8,
clones its pilot modulo 8B, and satisfies the cross square
requirements in the actual two-class construction. Put the
ordered x-squareclass coordinates at roots (0,Ds,Dt).
The exact marked cover has label

    alpha = (D,b,a).

## 1. Actual local Kummer images

For an odd prime p the size of E_D(Q_p)/2 is four, even at the
four moving bad primes. Indeed the compact local group has an
open formal subgroup on which 2 is invertible; the finite
quotient has the same size of its 2-kernel and 2-cokernel,
and its 2-kernel corresponds to E_D(Q_p)[2] since 2 is also
an automorphism on the formal subgroup. The two-torsion here
is the full four rational marked points.

Off B D the integral roots are distinct modulo p. Kummer
coordinates of any point are unit squareclasses: for v_p(x)<0
all three valuations equal v_p(x), which is even since their
product is a square; for integral x at most one factor can
have positive valuation and it must be even. The exceptional
derivative values for the two-torsion points are also units.
There are exactly four unit triples whose product is a square
at such odd p, so these are the entire local image.

At p|D all three root differences have valuation one since
p is outside B. For the marked 2-torsion T_i at e_i in the
order e=(0,Ds,Dt), use its usual exceptional coordinate

    kappa_i(T_i) = product_{j != i}(e_i−e_j),
    kappa_j(T_i) = e_i−e_j   (j != i).

The other Kummer tuple is (1,1,1) for O. Their valuation
parity triples are respectively the even patterns with
one zero at the marked index i, and the zero pattern at O.
These are four distinct local classes, exhausting the image.
Thus at each moving prime the parity pattern selects the
unique possible torsion representative before any unit tests.

## 2. The exact eight pair-supported classes and torsion independence

Consider triples d_j=a^(A_j)b^(B_j), where A and B are even
binary triples. This is an injective four-dimensional
squareclass parameterization, since a,b have disjoint nonempty
odd supports. All these classes pass every p|B and the real
place, since a,b are local squares there, and pass all good
places off B D by the unit image above.

In the two literal pilot rows the exact residues and characters are

| p | (s,t,s−t) mod p | Legendre signs |
| ---: | --- | --- |
| 415721 | (184830,322311,278240) | (+,+,+) |
| 9807649 | (4683094,7737981,6752762) | (−,+,+) |

The q_i clone these same *signs* because the rational values
are B-supported and q_i≡p_i mod 8B; −1 is square at all four
support primes. At either p|a, b is a local square: its
unit sign equals (s−t / p)=+ by the simultaneous local
solution at the a-contact. Similarly a is a local square
at either p|b, by (t−s / p)=+.

For p|a the candidate triple's parity is A and the unit
from the stripped first factor is (a/p / p) in every
coordinate of odd parity. The same stripped factor appears
in the permitted T_i precisely in those coordinates. It
cancels, since b and every root difference s_i−s_j are squares
in the residue, with s_i=0,s,t. The exceptional coordinate's
unit product is then square. Hence **every** A passes at both
p|a, independent of B.

For p|b the parity is B. Because a is a square unit, the
stripped b/p signs again cancel in the two odd coordinates.
With the exact signs in the second row, the only nonzero
allowed parity is the one at T_b, namely (1,1,0): both
differences from t are squares. For T_0 or T_a there is a
nonsquare difference involving s. The zero parity always
passes. Thus the pair-supported Selmer subspace is exactly

    W = { (a^A_j b^B_j)_j : sum A_j=0, B=000 or 110 }.

It has dimension three. The small replay checks all 16
tuples and both possible omitted stripped-unit signs
against the exact pilot residue table.

The global rational 2-torsion contributes an independent
dimension-two subspace T. Indeed its local parity rows at
any p|D distinguish it, so no nontrivial 2-torsion point
is divisible by 2 and there is no rational 4-torsion.
All odd torsion contributes zero modulo 2. Globally the
parity for a fixed T_i is the same at every prime of
support D; to lie in W would require A=B. The only
nonzero possibility is T_b with A=B=(1,1,0), whose
candidate W label is (D,D,1). But the actual first
coordinate of kappa(T_b) is D t, and t has nonsquare
class 2399. Thus T∩W=0. In particular

    dim_F2 Sel_2(E_D) >= 5        (at least 32 classes).

This rules out a minimal three-dimensional Selmer shortcut
for this particular paired family; it gives no bound from
below on the full 2-primary corank or the rank. The desired
alpha lies in W and is nonzero there, so is not the Kummer
image of any torsion point. Thus a rational point on the
marked cover already implies a nontorsion point on E_D.
In fact any rational point of C is in the nonzero affine
chart: Z=0 would imply a rational square root of a; w=0
contradicts t>0; U=0 contradicts s<0; V=0 would make t a
square. This does not place that point in the specified
p² and real open neighborhoods.

## 3. Reduce the first higher-descent test to four actual support primes

Here is a precise compact Cassels-pairing test on W,
without claiming its value. Use the tangent form of the
ordinary pairing [Shukla–Stoll, §3.2 eq. (3.10)](https://arxiv.org/pdf/2302.01640).
For C_alpha in coordinates [W:Z:U:V], the three exact conic
projections corresponding to omission of coordinate 0,1,2
in the ordered Kummer tuple are

    H_0: a U²−b V²−(t−s)Z²=0,
    H_1: W²−b V²−t Z²=0,
    H_2: W²−a U²−s Z²=0.

These come from subtracting the respective equations
d_i z_i²=x−e_i, with (z_0,z_1,z_2)=(W,aU,bV); omit
z_i in the i-th conic and divide by D. Each H_i has rational
points by Hasse–Minkowski, since its local points are
projections of the already locally soluble C. Choose
one rational point Q_i and primitive integer homogeneous
coordinates for it, and let L_i be the associated polar
linear form from the displayed diagonal coefficients.
Then for d' in W the pairing in signs is

    pairing(alpha,d') = product_v product_i (L_i(P_v), d'_i)_v,

with P_v local points on C avoiding the tangent zeroes.
Changing a rational scalar on any L_i has total product
one by Hilbert reciprocity.

Only the four primes of D need be tested for this pairing
on W. At all p|B and at infinity, each second argument
is a local square. At p outside B D, every nonzero
coefficient of the conics is a unit and the primitive Q_i
reduce to nonsingular points on their conics; the forms
L_i are nonzero after reduction. Their hyperplanes do not
contain the smooth degree-four complete intersection C mod p
(it is geometrically integral and nondegenerate). Each
therefore meets the curve in at most four distinct points.
There are >16 F_p-points by genus one and the Hasse bound
once a finite-field origin is chosen as in 7a597052.
Avoid the three tangents and Z=0, and lift the resulting
point with unit tangent values. The second arguments
are units there. The odd local Hilbert symbol of two
units is +. Hence none of these ordinary places leaves
an unknown global normalization term.

A basis of W is

    u=(a,1,a),  v=(a,a,1),  w=(b,b,1),  alpha=u*w.

The test against v is only

    P_a = product_{p|a} (L_0(P_p) L_1(P_p), a)_p,

and the test against w is only

    P_b = product_{p|b} (L_0(P_p) L_1(P_p), b)_p.

At the other pair of support primes the corresponding
second argument is a square unit, as proved above.
Alternation and alpha=u*w make the test against u
equal to the test against w. Thus two global conic
tangent choices and these two products of two local
signs suffice for all of W. This is a concrete second
descent reduction, requiring neither factoring the huge
fixed B pole data nor computing its separate pairing rows
to get a possible obstruction from W.

If either product is − this certifies C(Q) empty.
If both are + it only certifies orthogonality against W.
It is not orthogonality against the full Selmer group,
whose remaining classes are not bounded here. Even
full orthogonality means membership in the image of
Sel_4→Sel_2, not that the torsor class is zero
[Fisher, §1](https://arxiv.org/pdf/2208.14977).
This argument evaluates neither product: the required
tangent representatives vary with the actual unknown
q_a,q_b. The prior cloned Legendre and order data do not
supply their higher-phase values. It gives a sharply
localized exact next test, not an actual obstruction
to global points or proof of one.

Replay:
    python3 -B check_actual_pair_supported_selmer.py | cmp - EXACT-PAIR-SUPPORTED-SELMER.json
    sha256sum -c SHA256SUMS
