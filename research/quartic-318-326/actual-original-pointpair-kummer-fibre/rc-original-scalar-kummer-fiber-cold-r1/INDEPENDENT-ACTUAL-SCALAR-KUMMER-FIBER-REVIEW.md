# Independent cold review of the actual scalar Kummer fibre

**Exact paper and replay PASS, 2026-11-21.** The author manifest is
f05c4d664757f13587bce14e594cd8ad34c181adcb342e8520132956324900dd, the
paper f621d71b4edee8680719111ab743c9f9a371f6171629912b77b4ee9b22ac88b8,
and the author SHA256SUMS
bc8ba7655e36d23c1e3c3a9a0a455ba37f39a08249c4cc4727bdb40b6f3068fc.
All upstream hashes and the exact author JSON replay
f4ed8565184d24655508774f3278e5585e9a140bc4038f71fac87c9980d94ab6
were checked.

I independently verified the two directions in the exact
NormalizedPolePoints318.PointPair equations. If B=17b and z=T/B,
then z'=TBδ/s², and the ordinate divisors are βρ³ and βρ³s³, not
independently chosen scales. This gives the same rational conic in
both coordinates. The homogeneous conic parameterization satisfies
the equation and recovers every point (including t=∞).
For the reverse map, squaring its stated value of q gives
δ(a²−βb₀²)((a')²+3β(b'₀)²) divided by
((a²+3βb₀²)((a')²−β(b'₀)²)), precisely δz/z'.
Thus s=Bq is nonzero and both original equations hold with the same
T and second twist B²δ. When δ is nonsquare equality z=z' is
excluded; zero individual ordinates are legal in the raw interface
and are not discarded implicitly.

The two quartic quotient models and their common 2-covering
description have the correct involution T₀−P before a geometric
half-point is chosen. The stated birational Jacobian formula and
j=2048/3 check directly. The scalar twist keeps the branch
biquadratic field, not an S₄ field; the elliptic 2-division field
is Q(√−3), not rational full 2-torsion. These facts and the shared
potential multiplicative place at 3 prevent application of the
cited generic Kummer density theorems as stated
([Harpaz–Skorobogatov, Theorem A](https://msp.org/ant/2016/10-4/ant-v10-n4-s.pdf);
[Harpaz, §2](https://www.math.univ-paris13.fr/~harpaz/Kummer_second_descent.pdf)).
Nonintegral j excludes CM, and the unchanged nonsquare twist
reverses the primitive generator of geometric Hom.

Fix t'=1/c exactly. Then λ=1+3μ and V=c²W/δ give
V²=λ fβ(t,1) on the same surface. At 2,3 and odd β-primes
λ is square, and at other ordinary even-valuation places
the unit twist has smooth genus-one reduction. Its finite-field
point lifts. Negative λ valuations away from 2 and 3 have even
depth by the square denominator. At any other odd λ depth,
μ is a unit and −3βc² is 1 modulo the prime. The branch
t²=−3β therefore exists locally with simple root. Use the local
inverse function theorem around this actual branch, not a smooth
reduction claim for the nonunit-twisted equation, to obtain points
of nonzero ordinate. Local smoothness in all these cases, and
large real t at infinity, allow avoiding the finitely many
excluded affine parameters while retaining t'. The generic
parameter twisting extension is the rational conic
s²=1+3βc²; any map from it to the constant smooth genus-one curve
is constant, and a rational constant fixed by v↦−v would require
a rational branch root. Neither infinity is fixed.

The accompanying independent script uses inversion-free
Jacobian-coordinate addition and doubling in the genuine finite
curves over F_(p²), verifies the two annihilators before index
reduction, and re-evaluates the same scalar chart quantities.
For p=181 and 1346909, respectively, W_src reduces to 146 and
429536, the exact normalizer has depth 1, and the stripped
λ-units 84 and 268311 are nonsquares. Both λ depths are −2.
The author's independently implemented affine replay agrees.

The result is an everywhere-local fibre and a precise rational
arithmetic target for the unchanged original scalar. It does not
give a rational point in that fibre or on the Kummer surface, a
Brauer–Manin conclusion, a selected rank, or a four-pole grid.
No Lean or remote writes used.

Reviewed by the independent proof/CI lane.
