# In a prepared PointPair, a nonzero ordinate really gives positive rank

Let E_n be y²=x(x−n)(x+3n) over Q. For n≠0, any rational torsion point
with a nonzero ordinate has x-squareclass 3 or −1. We give a short proof
for this exact family rather than assuming a generic elliptic-rank
principle. The application is to *all* free twists appearing in the
source PointPair, not just the example where both coordinates happen
to be nonintegral. Torsion classifications for congruent-angle curves
are classical; compare the broader [general classification](https://www.mdpi.com/2227-7390/3/1/2).
The point here is the simple model-specific proof and its source
application, not a new general torsion classification.

## A uniform rational torsion calculation

Over K=Q(√n), of degree ≤2, the substitution x=nX, y=n√nY
identifies E_n with E_1. At p=5 and 7 the latter has good reduction
(all root differences are units). Over any place of K above p its
residue field embeds in F_(p²), including when the place ramifies.
Reduction injects the prime-to-p torsion into the reduced curve by
[Silverman, *The Arithmetic of Elliptic Curves*, VII.3.1(b)](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf).
Direct enumeration gives #E_1(F25)=32, #E_1(F49)=64. Thus any odd
prime torsion order is impossible: use 5 when the order differs from
5 and 7 when it equals 5. This avoids both Mazur's classification
and any need for n to be a unit at either prime.

For the 2-part, translate at any e∈{0,n,−3n} to X=x−e so that
Y²=X³+A X²+C X with C=(e−e')(e−e''). For Y≠0, the tangent formula
gives X(2P)=(X²−C)²/(4Y²). Therefore a point of order four, which
doubles to some (e,0), requires X²=C. At e=0 this would be −3n²,
at e=−3n it would be 12n²: both are impossible over Q. At e=n,
X=±2n, hence x=3n or −n. The respective ordinates satisfy y²=36n³
or 4n³, forcing n to be a positive rational square. These x therefore
have rational squareclasses 3 and −1, neither itself a square. But
the same doubling identity at e=0 says the x of a nonidentity
double must be a square. No rational point of order eight can double
to either of the order-four points. This also excludes larger 2-power
orders. The only remaining torsion points are O and the three y=0
points, proving the assertion.

## Source consequences

For b prepared, B=17b≠0 has odd 17-adic valuation, since b is a local
square at 17. V=B²(1−b/17)≠0. In a PointPair, the first and second
abscissas B and BS² for S≠0 both have odd 17-adic valuation. Hence
neither can have squareclass 3 or −1. The singular choice E=0 is
impossible: it would force y₁²=B³, which has odd 17-adic valuation.
The second curve parameter EV is nonzero as well.

Consequently each nonzero y_i in any actual PointPair gives a point
of infinite order on its actual E or EV twist. In particular the
previous two-nonzero family for every prescribed prepared first class
m now gives *simultaneously positive Mordell–Weil rank on the two
constructed twists*. The same conclusion holds for its exact global
two-seed product criterion, with no change of witnesses or additional
prime conditions. This does not assert rank on any preassigned n or
traditional canonical anchored twist, let alone original four-pole
existence.

If the complement is nonsquare, the two ordinates cannot both be zero.
Indeed E/B and EV/(BS²) would both lie in {1,−1/3}. Their ratio
V/S² is positive, so they must be equal, making V a square, contrary
to the nonsquare complement. Conversely a square complement permits
both zero via E=B, S²=V. Thus for a nonsquare complement the existence
of even an otherwise-unrestricted PointPair already gives positive
rank on at least one of its two twists; both ranks follow if both
ordinates are nonzero.

At the explicit b=(204/1073)² with complementary class 409, the
prior disjoint anchor obstructions prove no zero-ordinate solution
is possible. Its displayed pair therefore witnesses simultaneous
positive rank. As a redundant direct independent test, scale the
two rational parameters by rational squares to integral twist
parameters 3026 and 1237634. Their actual x-coordinates become
71825/16 and 5161217/4. On the integral short models
Y²=X³−351N²X+1890N³, X=9x+6N and Y=27y, these remain nonintegral;
this also gives infinite order by Nagell–Lutz. No global Mordell–Weil
basis or exact rank is concluded. Stdlib verify.py recomputes both
finite-extension counts, integral twist scalings and short equations.
