# A genuinely different genus-one route to the fixed scalar's PointPair

Take the same exact scalar b at the materialized h,J, same β and c,
and set D=βc²=b/17, δ=1−D. The proof uses no ξ, τ or reduced
denominator character from the previous chart, and does not need to
extract the full squarefree part of δ. Claim: the smooth projective
curve below is everywhere locally soluble for this actual scalar;
**a rational point on it would give the literal PointPair**, but
no rational point is established here.

## New curve and exact marked transport

Let X_c be the intersection of the two quadrics
    U² + 3β X² = 4Y²,
    V² + 3β(X+cY)² = 4(Y+βcX)².
For x=X/Y put y=(x+c)/(1+βcx). Use the rational parametrization
    φ(t)=4t/(βt²+3),
    (2(3−βt²)/(βt²+3))²=4−3β φ(t)².
The two conics give rational t,s with φ(t)=x and φ(s)=y:
for instance t=(2+U/Y)/(βx); the analogous rational root formula
uses V/(Y+βcX) for s.

In K=Q(√β) set
    R(t)=βt²+3+4t√β,
    f(t)=Norm(R(t))=(βt²−1)(βt²−9).
Equality φ(s)=(φ(t)+c)/(1+βc φ(t)) is exactly proportionality
of R(s) and (1+c√β)R(t) by a common nonzero rational factor
r (compare their rational coefficients). Taking norms gives
    f(s)=r² δ f(t).
Put n=β f(t). The standard exact formulas
    R₀=βt²+3,  u=2(3−βt²),  v=4βt,
    x_E=βR₀²,   y_E=βR₀uv
give the literal mark (x_E+3n,x_E−n)=(βu²,v²).
Using s gives a second marked point for nδr²; scale by r to
get the marked point for nδ. If retaining the original squarefree
θ, use δ=θe² and scale the companion by er instead. Neither
version changes b or the point equations.

In fact the literal PointPair API permits using the rational
companion scale δ itself: B=17b, c_API=17c, d_API=B then
    B=β c_API²,  B²(1−b/17)=δ d_API².
The marked pair on E_n, E_(nδ) then gives the exact output by the
existing actual Kummer point extraction, not by a new polynomial.
No rank-one theorem, denominator normalization, or selected
prime conditions are needed to verify this direct output.
This is a sufficient construction, not equivalent to all possible
PointPairs or to the previous one-variable cut.

There are no rational chart exceptions at the actual scalar:
* Y=0 is impossible over R, as is Y+βcX=0 by the second
  square and δ≠0.
* x=0 and x=−c both require 4−3D square; D≡8 mod13
  gives the unit 6, nonsquare.
* βt² and βs² never equal 1,3 or 9 in Q, since the actual
  β represents neither the squareclass 1 nor 3.

Thus any rational point of this exact X_c supplies the
nondegenerate marked pair without an odd-multiple argument.
It has not been obtained merely by the following local checks.

## Smoothness and actual all-place local solubility

The two branch quadratics in [X:Y] are
    q₁=4Y²−3βX², q₂=4(Y+βcX)²−3β(X+cY)².
Over characteristic not 2,3, where β and δ are units and c is
integral, both have simple roots. If u=√β X/Y is a root of q₁
and e=√β c, then u²=4/3 and q₂/Y²=e(2u+7e/3).
For e≠0 a common root therefore occurs exactly at 49D=48
(and exactly one common root there outside characteristics 2,3,7).
Since the actual 0<D<1/9, the branch sets are disjoint over Q.
The resulting degree-four map to P¹ has two ramification points
of index two above each of four base branch points; Riemann–Hurwitz
gives genus one. The projective complete intersection is smooth
when the two branch sets are simple and disjoint.

At the real place choose x close to 0 and y close to c; both
discriminants are positive. At 2 take x=1: c has valuation 2,
β≡1 mod8, and y remains a unit. Both squared ordinates then
are units 1 mod8. At 3, c is integral and x=0 gives
discriminants 4 and 4−3D≡1 mod3. At p|β, including 5,
c is integral, D≡0, and x=0 gives nonzero square residues.
In each local case one can perturb x a little if a boundary
value is unwanted.

For other odd p with integral c:
* If D≡0 or 1, again x=0 works, with q₂ residue 4 or1.
* At 49D≡48 (necessarily p≥11 after the special places),
  both branch quadratics split with exactly one common root:
  3β is square because βc²=48/49. For x outside the three roots,
  the three functions χ(q₁), χ(q₂), χ(q₁q₂) are each characters
  of separable quadratic polynomials after canceling a square in
  the last case. Each sum on the allowed x has absolute value ≤2
  (full quadratic character sum up to omitting a single nonzero
  term). Thus at least (p−9)/4 choices make both values nonzero
  squares. Unit Hensel proves local points of the true quadrics.
  The exact actual p=83 is such a place, with 49D−48≡81·83
  mod83², and an explicit smooth pair x=2, (q₁,q₂)≡(9,28).
* Else the simultaneous double cover has good genus-one reduction.
  At p=7 the actual c≡1, D≡2, so both forms are simple and
  disjoint (in characteristic 7 the common-root expression is
  2eu ≠0). Hasse and smooth lifting apply.

If v_p(c)<0, then p≥11, p∤β by the checked scalar units
(in particular p is not 7). Rescale the second ordinate by c
before reducing; the second quadratic becomes
4β²X²−3βY². Its roots and those of q₁ are simple and disjoint
because 16≠9 modulo p. Hence good reduction and Hasse again.
These cases exhaust all local places.

## Arithmetic feasibility and why this is a different problem

The determinant of the symmetric quadric pencil is exactly
    β λ μ [−12 λ² + (25D−24)λμ −12δ² μ²].
By the determinant-quartic Jacobian formula for a quadric
intersection (see [Fisher, Higher descents §8](https://www.dpmms.cam.ac.uk/~taf1000/papers/higherdesc.pdf)),
the actual Jacobian is isomorphic over Q to
    y²=x[x²+β(25D−24)x+144β²δ²].
The sign is retained by the change x=−12βλ in the μ=1
chart of the determinant equation. This elliptic curve
has an actual point of order four at
    K=12βδ,  (x,y)=(K,βc K),
since the model is x[(x−K)²+(βc)²x].
It has a different extra discriminant factor β(49D−48),
not β(25D−9) from the older genus-one cut. In particular
these two generic Jacobian families cannot be isogenous over
Q(c), since one has multiplicative reduction at 49D=48
and the other has good reduction there. This does not
predict the ranks of the particular materialized fibers.

Both rank-three conics have explicit Q origins ((x,U)=(0,2),
and use x=−c,V=2δ for the second), permitting a separate
tangent-pushout or genuine 2-descent analysis of this new curve.
All-place solubility of a genus-one curve does not prove Q
solubility. Nor is a universal rational parametrization in c
available: for p|β and v_p(c)<0, primitive X,Y require Y a unit
by the first equation, but the second divided by c² then has
right-hand side of valuation one. This gives infinitely many
rational c with no Q_p point and precludes a generic Q(c) point.
The actual c has none of those forbidden valuations.

The larger two-variable pairing surface is the Kummer model
z²=δ f(t) f(s), a product of the two marked 2-coverings.
It is not justified to import a general Hasse principle:
for example the private split-multiplicative places in
[Skorobogatov–Swinnerton-Dyer, Theorem 1](https://www.ma.imperial.ac.uk/~anskor/SSD_AM.pdf)
are not available for two twists of the same base x(x−1)(x+3).
At every odd p≥5 the three root differences of either twist
have equal valuation, and at 3 the actual δ is a unit square
so the two twists have identical local reduction. The new
curve above is a distinct arithmetic route, with an exact
one-curve target and a verified output if that target is solved.

## A concrete first arithmetic obstruction target for this new curve

The quotient by simultaneous negation of the two conic ordinates
has affine equation z²=q₁(x,1) q₂(x,1). Put k=z/q₁(x,1);
the quadratic q₂−k²q₁=0 has coefficient
A_x=β(4D−3+3k²) at x² and linear coefficient 2βc. Thus
    H_x=A_x x+βc,
    H_x²=β[12k⁴+(25D−24)k²+12δ²].
The exact map (x_E,y_E)=(12βk²,12βkH_x) gives the same
Jacobian curve displayed above, with actual x-class 3β.
For a rational point of X_c, q₁,q₂ are nonzero (3β is nonsquare)
and k=V/U is nonzero. Consequently a first global necessary
condition on the alternative route is that 3β be represented
in this new Jacobian's rational x-class group.

This would in particular require positive Mordell–Weil rank.
Its nonzero rational 2-torsion is unique since the quadratic
factor discriminant is β²D(49D−48)<0. Its known order-four
point has class 3βδ, not 3β; this class is nonsquare also
since v₃(3βδ) is odd. No rational order-eight point can halve
either order-four point because their x-class is nontrivial
and doubling kills x-classes. Odd torsion maps to 1. Thus a
rational point of class 3β cannot be torsion. This test is
different from the old x-class-β / ξ analysis; neither need
be assumed from local solubility of the other.
