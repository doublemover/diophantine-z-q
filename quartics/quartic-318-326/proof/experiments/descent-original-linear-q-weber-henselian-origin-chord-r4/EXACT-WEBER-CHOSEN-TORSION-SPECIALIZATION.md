# Prime-to-p specialization of the chosen Weber generator

## Statement and scope

Let K=Q(i), E: y²=x³−x, M>0, and T=K(E[M]). Fix a place
P of T over a finite prime 𝔭 of K of odd residue characteristic p
with p∤M. Let R be its valuation ring, F its fraction field, k its
residue field, and write ξ for the residue of the SAME i in R.
Consider the point P₀ chosen earlier as a generator of E[M] over
Z[i]/(M), not a residue frame chosen anew. Then

1. specialization by primitive homogeneous coordinates is injective
   on E[M](F). More exactly, equality of specializations of any
   generic points implies that their difference lies in the origin
   chart kernel, and this kernel has no nonidentity M-torsion.
2. Coordinate reduction is an additive homomorphism on this
   literal curve and commutes with the same Gaussian turn. Inertia
   at P fixes P₀ and all of E[M], so T/K is unramified at 𝔭.
3. On the split branch N𝔭=p, if the already separate geometric
   residual statement says that the arithmetic p-coordinate Frob
   on the specialized P₀ is [ε π] bar(P₀) for a generator π of THIS
   𝔭 and a single ε∈μ₄, then the arithmetic Artin element on T
   satisfies σ(P₀)=[ε π]P₀. Thus the Weber value x² has tag [π],
   with no independent sign choice or inverse convention.

This gives a short alternative to importing a general smooth
proper-group-scheme point specialization or a complete formal-group
development. The proof of injectivity is ordinary chord/tangent
algebra on the literal curve; not the arithmetic Frobenius degree
or differential theorem it consumes. No cardinality of the
special-fibre torsion, henselization/étale equivalence, or formal
inverse is required for these conclusions.

## 1. Primitive homogeneous coordinates and the origin

Normalize a homogeneous triple [X:Y:Z] by choosing a minimum-valuation
nonzero coordinate and dividing all coordinates by it. The reduction
then has a unit coordinate, remains on Y²Z=X³−XZ², and is independent
of the triple: two primitive representatives differ by a valuation-zero
scalar. At Z=0 the only point of this special fibre is [0:1:0].
If the specialization is affine, then Z is a unit in every primitive
representative and affine x=X/Z and y=Y/Z are integral. In particular,
if x is not integral, specialization must be the origin.

Write t=−X/Y, w=−Z/Y near the identity. The literal normalized
representative is (−t:1:−w), with t,w in the maximal ideal for every
point specializing to the origin. Its exact equation and turn are

    w+t w²=t³,     J(t,w)=(i t,−i w).

Negation reads (t,w)↦(−t,−w); t=0 implies w=0 and the point is
the identity. For later use, w belongs to (t³) since
w(1+t w)=t³ and the bracket is a unit.

Optional native lift of the whole chart: for any t in the maximal
ideal of a henselian local ring solve the monic equation
rho²+rho−t⁴=0 with rho in the maximal ideal (the derivative
at 0 is 1); set w=t³/(1+rho). Then t w=rho by the equation,
even if t=0 or is a zero divisor. Uniqueness follows from
(w−w′)(1+t(w+w′))=0 and the second bracket being a unit.
This also sees the actual tangent: mod any square-zero ideal with
t,w in it, w=0 and J acts by t↦it.

Optional ordinary lift: at a point (x₀,y₀) over k, if y₀≠0 choose
any lift x and solve the monic equation Y²−(x³−x)=0 in the
simple class y₀. If y₀=0 choose y=0 and solve the monic equation
X³−X=0 at x₀, whose derivative is −1 at 0 and 2 at ±1.
Odd residue characteristic is exactly what this argument needs.

## 2. The literal algebraic kernel multiplication

For two origin-chart points (t₁,w₁),(t₂,w₂) set

    λ = (t₂²+t₁t₂+t₁²−w₁²)/(1+t₂(w₂+w₁)),
    ν = w₁−λt₁.

The denominator is a unit. Subtract the two chart equations to see
w₂−w₁=λ(t₂−t₁); actual distinct points have distinct t, by
uniqueness above even without Henselianity. For coincident points
the displayed λ is the implicit tangent slope, because the partial
derivative in w is 1+2tw. Thus this is the actual projective
secant/tangent in the Y=1 chart, including the identity. In the
standard geometric group law three intersections (with multiplicity)
on a line sum to zero. Here substitution w=λt+ν gives

    (1−λ²)t³−2λνt²−(λ+ν²)t−ν=0.

The leading coefficient is a unit (λ lies in the maximal ideal),
so there is no missed intersection on Y=0. The third root is
2λν/(1−λ²)−t₁−t₂; it and its w-coordinate are small. Its
negation gives the exact same-chart group law

    t(P+Q)=t₁+t₂−2λν/(1−λ²).

Thus the kernel is a subgroup. If t₁,t₂ both lie in (t), with
t in the maximal ideal, then w₁,w₂ lie in (t³), λ lies in
(t²), ν lies in (t³), and the last correction lies in (t⁵).
Induct from the identity, adding one fixed P with t=t(P), to
obtain

    t([m]P)=m t+t⁵ c_m,     c_m ∈ R         (m≥0).

(In particular every intermediate parameter lies in (t).)
When p∤M the equation t([M]P)=0 forces
t·(M+t⁴c_M)=0. The second factor is a unit since its residue
is M. Hence t=0 and P is the identity. This is stronger than
the usual first-jet t([M]P)=Mt+t²R needed for injectivity.

## 3. Equal reduction implies kernel difference without importing additivity

It remains to cover points with an equal *affine* specialization.
If P=(x,y), Q=(X,Y) and bar(P)=bar(Q)=(x₀,y₀), the four
coordinates are integral by §1. The equation gives the exact identity

    (y−Y)(y+Y) = (x−X)(x²+xX+X²−1).

If x≠X, the slope for P−Q is λ′=(y+Y)/(x−X).
* If y₀≠0, its numerator is a unit (p is odd) and its denominator
  has positive valuation. Hence v(λ′)<0.
* If y₀=0, then x₀∈{0,±1} and D=x²+xX+X²−1 has
  nonzero residue 3x₀²−1. The displayed identity implies
  y−Y≠0 and λ′=D/(y−Y), again of negative valuation.

If x=X then y=Y gives P=Q, and otherwise y=−Y≠0.
Equal reduction forces y₀=0 since p is odd, and P−Q=[2]P;
its tangent slope (3x²−1)/(2y) has negative valuation by the
same derivative argument. In every nontrivial branch, the affine
addition formula x(P−Q)=λ′²−x−X has negative valuation, because
x and X are integral. Thus P−Q specializes to the origin by
§1. If both reduce to the origin, use its subgroup from §2.
This proves the difference criterion and injectivity on M-torsion
without demanding the full addition compatibility on *all* pairs.

## 4. Full additivity on this literal model, if needed

This section recovers compatibility with integer multiplication
without invoking the general good-reduction homomorphism.

First, translation by a kernel point T does not change any affine
specialization. The trivial T is immediate. Otherwise parametrize
it as in §1 with t≠0. In this paragraph O(t^j) means exactly an
element of the principal ideal (t^j) in the valuation ring; it is
not a real-analytic asymptotic. From the chart equation,
w=t³/(1+t w)=t³+O(t^7). For the affine point P=(x,y) with
integral coordinates, the secant with T has slope

    l = (−1−y w)/(t−x w)
      = −t⁻¹(1+x t²+y t³+O(t⁴)).

The equality follows by multiplying (1+x t²+O(t⁴)) by
(1−x w/t); the latter is a unit. The original T has
x-coordinate t/w=t⁻²+O(t²), so the literal affine formulas give

    x(P+T) = x+2y t+O(t²),     y(P+T) = y+O(t).

For the second formula use (y(P+T)=−y+l(x−x(P+T)));
the leading correction is (+2y). Thus the same residue is
obtained. Both-kernel addition is already §2.

Next, two affine specializations with different x-coordinates
have an integral secant slope and the usual affine formula reduces
termwise. Two points with opposite specializations have sum in the
kernel by §3 applied to the negative of one of them. The remaining
two affine inputs can be treated using one auxiliary point over
an algebraically closed valued field extending F. Its residue
field is algebraically closed: lift each monic polynomial,
its roots upstairs are integral, and reduction gives a split
factorization downstairs. Every affine residue point has an
upstairs lift by first lifting its x-coordinate and then choosing
the sign of an upstairs square root to match the residual
y-coordinate on the literal equation. The root is integral by
its monic equation. No unramified extension theorem is needed for
this verification of identities of the original specializations.

In this enlarged field write p₀,q₀ for the affine specializations
and b₀=p₀+q₀, which is not the identity in the remaining case.
Choose an auxiliary affine residue point a₀ such that each pair

    (q₀,a₀),     (p₀,q₀+a₀),     (b₀+a₀,−a₀)

is affine with different x-coordinates. Only finitely many are
excluded: excluding a zero coordinate and equality up to sign in
the first two pairs removes finitely many points by translations;
in the last pair equality up to sign would force b₀=0 or
[2]a₀=−b₀, and the latter has finite fibre. For this small
fact, an affine non-2-torsion point has
(x([2]A)=(x(A)^2+1)^2/(4(x(A)^3-x(A)))),
so a prescribed finite value gives a nonzero monic quartic;
the identity fibre has only the three y=0 points and infinity.
There are infinitely many affine x-values over an algebraically
closed field and the finite forbidden set can be avoided.
Choose any integral lift A of a₀. Apply the good secant case
to Q+A, then P+(Q+A), then P+(Q+A)−A. Associativity on the
field point groups gives the desired equality for P+Q. The
original specializations lie in the original residue field, so
equality after this inclusion suffices. Together with the
literal homogeneous quarter turn, this proves compatibility
with every [a+bi] under the same embedded i.

## 5. Galois comparison and the legitimate stopping point

An automorphism in the decomposition group preserves the valuation
ring. Transforming a primitive homogeneous representative by it
commutes with coordinate reduction and the induced residue
automorphism. Inertia acts trivially on the residue, so each
torsion point equals its inertia conjugate by §§2–3. For a
split prime, arithmetic Frobenius induces the positive p-coordinate
power on k. Once the denoted residual geometric-action identity
in item 3 has been obtained (using degree p, the same-𝔭
differential, and one global unit), the just-proved compatibility
with [επ] and injectivity give the equality of the two actual
torsion points. No separately chosen generator may be substituted.
This proof does not construct the global torsion field, geometric
degree, residual Gaussian Frobenius identity, or the joint
affine-prime asymptotic.

If one wants genuine surjectivity on geometric M-torsion as well,
pass to algebraic closures; in residue characteristic not dividing
M both geometric [M] kernels have size M² by the separable
degree theorem, so the injection is a bijection. That theorem
is unnecessary for the chosen-generator arithmetic comparison.

### Native source boundary

* HenselianChart: exact monic Hensel construction, uniqueness, break
  to the tangent at a square-zero ideal, and unit-linear kernel algebra.
* HenselianAffineLift: genuine ordinary lift of every affine point
  of the odd special fibre by the pinned monic one-variable Hensel API.
* FormalChord: algebraic divided difference and t⁵ order certificates
  for the actual chart; it does not apply the affine native group law.
* DVRIdentity: links the chart to the literal Mathlib Projective
  equation, plus true specialized origin and same-i quarter turn.
* SpecializeChosen: reuses literal affine native points, their actual
  Gaussian action, and the positive coordinate Frobenius. It gives
  injection, inertia identity and the exact chosen-point arithmetic
  identity once the projective red hom and first-jet input are
  supplied, using their actual types. It does not claim that stock
  coefficient `HasGoodReduction` supplies them. The native geometric
  omissions are the homogeneous normalized DVR reduction (including
  point group-law compatibility), and enabling small-chord multiplication
  on the actual group. §§3–4 are the exact elementary route to
  that missing native reduction law rather than assumed geometry.

Pinned source at Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679:
Henselian.lean e2b4217378edf1631a6f580166e502c3f9233f93, lines
94–153; ResidueField/Basic.lean 5f9b0440c80e58610c5f91503ca91d55d5f2ba88,
lines 37–43; Projective/Basic.lean 5a21057d28940b24a1bcd93286bb7c5e86511c67,
lines 235–285 and 366–372 (the ring `Nonsingular` still only
numerically accurate over fields), Projective/Point.lean
9406356c8f6a8cb471ebdb6c283cd8ea33602ae8, lines 398–423 and 612–617
(group addition over fields/base change, not DVR points).
Primary background: [Silverman, AEC III.2 group law and VII.3
prime-to-p kernel](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf).
[Stacks, Tag 04GK](https://stacks.math.columbia.edu/tag/04GK) is
the more general finite-étale lifting route; it is not a native
dependency of the elementary chosen-generator proof.
