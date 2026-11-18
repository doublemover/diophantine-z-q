# Two nonzero rational ordinates at exact prepared depths (research)

**Result.** In every open real subinterval of (0,17) there is a rational b
with square reduced denominator, local squareclass one at 2,3,17, and
(v2(b),v3(b),v17(b))=(4,2,2), admitting an actual normalized PointPair
with both ordinates nonzero. All constructed b have the same **nonsquare**
class 9145=5·31·59 and their complements 1−b/17 have a second fixed
nonsquare class. The two squareclasses are distinct (at 41, 9145 is 2,
a quadratic residue, whereas the complement class is 12, a nonresidue).
Neither a rank theorem nor a distribution conjecture is needed here.

This is a conditional consumer and a constructive family of **individual**
rational poles, not a solution of the original common-index problem. The
scalar depths coincide exactly; this does not identify even one pole with
the scalar circuit at any specified input. The row classes could differ from
9145. No original integer assignment, order tuple or quartic equivalence follows.

## 1. Actual target and transfer

Write B=17b, V=B²(1−b/17), F_n(x)=x(x−n)(x+3n). A PointPair has the same
E in y1²=F_E(B), y2²=F_(EV)(B s²), with s nonzero. We construct rational
E,s,y1,y2, not merely locally soluble curves. Starting from a genuine pair
at b0, suppose b=b0 X² and 1−b/17=(1−b0/17)Z² with XZ nonzero. Then
B=B0 X², V=V0 X⁴Z². Set

    E=E0 X²,   s=s0 X² Z,   y1=y10 X³,   y2=y20 X⁹ Z³.

Indeed F_(n t²)(x t²)=t⁶ F_n(x). Scale the first curve by t=X and the
second by t=X³ Z. Its abscissa becomes B0 s0² X⁶ Z² = B s² and its
parameter E0 V0 X⁶ Z² = E V. The inverse uses 1/X,1/Z. Thus the two
global squareclasses transport actual points both ways and cannot change a
zero ordinate to a nonzero one. A PointPair also gives a literal Realization
by taking β=B, θ=V, c=d=1, roots 1,s, and n=E. These representatives need
not be squarefree; the structure does not require it. The source certificate
at this same b (nonzero) has e=E/b, s_source=s/b, p=y1/B,
q=17y2/(B³s). No assertion about the order or rank of a point is necessary.

## 2. A seed on two nonsquare classes

Set m=9145, N=17m, a=1297/532, Y=149622419334526725/150568768.
Direct integer multiplication gives Y²=F_N(N a²), Y≠0. One way to find
the point was to add the 2-torsion (N,0) to twice the point
(−295885,150901350) on F_N; verifying the single cubic suffices.

Take τ=48/691, σ=14/691, so 51τ²+mσ²=4, and w=17τσ.
Set b0=m w²=1193493611520/227988105361, B0=17b0=Nw²,
u=2−51τ². These give 4−3b0/17=u². The old one-torsion specialization
with E=B0 and s=B0 has a usable **second** point: its ordinate B0⁴ b0 u
squares to F_(B0 V0)(B0³), since putting d=1−b0/17 reduces the RHS to
B0⁹(1−d)(1+3d). Instead of using its zero first ordinate, take the
constant-curve point scaled by w, with abscissa B0 a² and ordinate w³Y.
Rescale both curves by 1/a to bring the first abscissa back to B0. Now

    E0=B0/a²,   s0=B0/a,   y10=w³Y/a³,   y20=B0⁴ b0 u/a³.

Every factor used is nonzero. The complement d=157782598801/227988105361
is 12 modulo 41; 12²⁰≡−1 mod 41. Also 9145≡2 mod 41 and 17²≡2 mod 41.
Thus even the two nonsquare classes are distinguishable; neither class
has been obtained by replacing the corresponding source value.

## 3. Full exact local preparation and real density

Let c=b0/17, d=1−c. The rational conic cX²+dZ²=1 has seed (1,1).
Intersecting the line Z=1+λ(X−1) through that seed gives the second root

    X=(dλ²−2dλ−c)/(c+dλ²),   Z=1+λ(X−1).

Take M=32·3·17·5·31·59 and λ=16+M j/7^k for arbitrary integer j and
nonnegative k. Since c,d>0, the denominator is always nonzero over Q.
Discard the finitely many λ with XZ=0. Then 0<b=b0X²<17 and §1 gives
both nonzero ordinates.

At 2 the seed has v2(c)=10 and d is a unit. Since v2(λ)=4, the three
numerator terms above have valuations 8,5,10 and the denominator terms
10,8. Both minima are unique; hence v2(X)=−3 and v2(b)=4. At 3,17
we have c≡0 and d≡1; λ≡16 and neither 16 nor 14 is zero. Thus X is a
unit and the seed's v3(b0)=v17(b0)=2 are retained. The seed depths follow
directly from w=17·48·14/691. The local squareclasses are those of m,
which is 1 mod 8, 1 mod 3 and 16 mod 17, hence a square at all three
places (the unit-square tests at 2 and the odd-prime Hensel lifts).

**Every denominator prime:** b=m(wX)². Any prime outside 5,31,59 has
even valuation. At each of 5,31,59 the seed w is integral, c≡0,
d≡1, and λ≡16 is a unit. Thus c+dλ² is a unit, X is integral,
and b has nonnegative valuation. This proves the *reduced* denominator
is square without an uncontrolled new bad prime.

The slopes chosen are dense in R (mesh M/7^k tends to zero). Every target
b* in (0,17) occurs on the real conic: take X*=−sqrt(b*/b0) and
Z*=sqrt((1−b*/17)/d). Then X*<0, so (X*,Z*) is not the starting point
and its secant slope is finite. The displayed second-root formula gives
exactly X*,Z*. Continuity gives slopes of the required arithmetic form
whose b lie in any prescribed open subinterval about b*. This proves density
without assuming anything about a rational orbit visiting these slopes.

Example λ=16 gives

    b = 22658301122605409802222416195208720/5695590725813967968465563114286281.

This family escapes not only the square-complement case but also the
earlier one-torsion test itself: for a locally square b of v2=4, write
b=16h, with h a 2-adic square unit. Then (4−3b/17)/4=1−12h/17≡5 mod 8.
So 4−3b/17 is *not* a rational square at the transported poles, even
though we used that older test at the auxiliary seed of v2=10.

## 4. A negative check on the fixed preparation parameter

At 17, if v17(b) is even and ≤0, then v17(B) is odd and v17(V)=
2v17(B)+v17(b)−1 is odd. Write e=E/B. A rational solution of the first
curve would force e to be a 17-adic unit: e=0 or positive valuation
makes f(e)=(1−e)(1+3e) a unit; negative valuation gives even v(f(e));
in either case B³f(e) has odd valuation. Its zeros 1,−1/3 are units.
The second equation similarly forces eV/s² to be a unit, since it has
the same B squareclass. But v17(V) is odd and v17(s²) even. Impossible.

In particular b=1 cannot simply use the preparation-zero PointPair. This
does not refute the manuscript: its seven-witness preparation permits t
to vary, and the **fixed** t=0 completeness assertion separately requires
v17(b)≥2, exactly excluding that example.

## 5. Provenance, scope and verification

Source base a0950ac7c24df6d336a196966fb790d6abd55e44. Read the original
quartic_v10.tex preparation-zero bridge and simultaneous-realization lemma;
the actual r155 NormalizedPolePoints318, TwoTwistPointRealization318,
OneTorsionPoleFamily318, TwoTorsionTwistRealization318,
PositiveSquareclassPole318, ActualFourPoleClassMatching318 and
ActualFourPolePreparation318. Earlier one-torsion and equal-twist results
are prior art; the new construction combines a nonzero first ordinate,
a fixed nonsquare complement and class-pair transport to achieve exact
scalar depths, with two nonzero ordinates on a real-dense set. No historical
acceptance is carried forward to this change. The original fifteen-position
prime/order arithmetic is unchanged and unresolved in this packet.

Run `python -B verify.py` and compare to FINITE-REPLAY.json. The program
substitutes exact fractions into both original cubics and both factored
source equations; its finite grid is not the density proof. The small
PreparedPairTransport318.lean source is a draft for the algebraic transfer,
consumer and numeric seed, not a Lean proof of local preparation or density.
It was not compiled locally and no hosted acceptance is asserted. No
production source, manuscript, workflow or release state changed.
