# Two nonzero rational ordinates for every prescribed prepared first class

**Result.** Fix any positive squarefree m square over Q₂,Q₃,Q₁₇.
The previous arbitrary-m producer allowed a zero first ordinate. Here both
ordinates are nonzero for a real-dense family of prepared b in class m,
with exact depths (4,2,2), square reduced denominator, and marked
nonsquare complement. More strongly: for any already specified prepared
target b* of class m, such pairs approximate b* simultaneously at any
finite set of places while preserving all its local complementary classes
there and its actual depths at 2,3,17 (which need not be (4,2,2)).
The construction needs neither a non-torsion point on the fixed twist
of m nor any rank hypothesis. It applies, in particular, to the literal
scalar first class at integer input zero and the exact five-prime product
of the previously certified original model row.

There is a separate **exact global** implication, not just approximation:
if the target complement class is the product of two indicated seed
classes, the resulting point-pair transports *onto b* itself*, with both
ordinates nonzero. We do not establish this product condition for the
four particular poles of one original assignment. The general
approximation deliberately uses a differing global complement.
The common first twist E below is free; no fixed canonical anchored
twist, positive rank, full source witness or Lean acceptance follows.

## 1. Two points on the same elementary parameter conic

Write β=17m, B=17b, V=B²(1−b/17), F_n(X)=X(X−n)(X+3n).
For nonzero rational x define

    e_x=(x²−β)/(x²+3β),        P_x=4βx/(x²+3β).

Then β(1−e_x)(1+3e_x)=P_x². Independently choose nonzero rational
parameters λ,μ and put

    s=(λ²−3β)/(2λ),   J=(λ²+3β)/(2λ),
    t=(μ²−3β)/(2μ),   K=(μ²+3β)/(2μ).

Thus s²+3β=J² and t²+3β=K². Initially take s²,t²>β, s≠t,
st≠β (for example s,t>√β and distinct). Put

    h=(s−t)/(st−β),   w=17h,    b₀=m w²,    D₀=1−βh².
    T= K(s²−β) / (J(st−β)).

Two identities give the construction:

    D₀=(s²−β)(t²−β)/(st−β)²,      T²=D₀ e_s/e_t.

Thus 0<D₀<1, b₀=17(1−D₀)∈(0,17). Put B₀=17b₀=βw²,
V₀=B₀²D₀. An actual PointPair, with the literal common twist E, is

    E=B₀ e_s,      S=B₀ T,
    y₁=w³ β P_s,   y₂=(wS)³ β P_t.

Indeed E/B₀=e_s and EV₀/(B₀ S²)=e_t. Therefore F_E(B₀)=
B₀³(1−e_s)(1+3e_s)=y₁², and the analogous evaluation at B₀ S² is
y₂². All of E,S,y₁,y₂ are nonzero. This is not a construction of two
independent twists. The parameter symbols s,t are not the output S.
A nonzero ordinate is not a proof of infinite order.

## 2. What the construction reaches exactly

Define f(λ)=(λ²−β)(λ²−9β)/(λ²+3β)². Direct substitution shows that
e_s=f(λ) and e_t=f(μ); this is precisely the old single-seed complement
function, with λ=17r in the earlier c=m/17 notation. Now

    D₀ = f(λ) f(μ) [JK/(st−β)]².

Suppose b*=m v²∈(0,17), v≠0, and D*=1−b*/17 has a nonsquare class
equal to [f(λ) f(μ)] over Q. The finite nonzero λ,μ here need not satisfy
the positivity convention in §1: positivity of D* already forces
(s²−β)(t²−β)>0. Neither s nor t can vanish (3β is nonsquare).
The equality st=β would give negative product; s=t would give square
product class. Thus all the same formulas are defined and give 0<D₀<1
and a genuine pair. Choose X=v/w and Z with Z²=D*/D₀. At b=b₀X²=b*
transport by

    E'=EX², S'=SX²Z, y₁'=y₁X³, y₂'=y₂X⁹Z³.

The two equations follow from F_(n a²)(x a²)=a⁶ F_n(x); neither
ordinate is lost. Conversely a class produced by this restricted
two-hyperbola construction and transport is visibly such a product.
This characterizes THIS parametrization, not all PointPairs. The square
class [1] also works, e.g. t=−s, s²>β (use μ=−λ). The earlier
single-seed d=1 condition tests one factor, not the product condition;
we do not assert that a particular known insoluble single-cover example
has a representation by two factors.

## 3. Arbitrary finite-place approximation with an explicit new global marker

Here prepared means 0<b*<17, square reduced denominator, local squares
at 2,3,17 and respective depths at least 3,1,2. Write b*=m v².
Enlarge a prescribed finite set of places to contain infinity, 2,3,17
and all primes of m. Call it S₀. Choose nonzero rational λ with s>√β
such that e_s is a local square at every finite p in S₀: the rational
function f(1/x) tends to 1 as x→0, and the square class of 1 is open
there. One can take λ with arbitrarily large denominators at those
primes and large positive real size (e.g. choose integer numerator
congruent 1 at all and sufficiently large after fixing the denominator).
Exclude λ at finitely many exceptional values.

Choose a fresh prime q outside S₀, the supports of e_s and D*, and
any further finite avoidance list, with β square mod q. For instance
take a prime factor of βH²−1>1, where H is a multiple of all excluded
primes and 6β. This avoids βH and gives a square root of β mod q.

Use the **previous finite-place seed lemma** (forward-canonical-anchor-
finite-place-closure-r1, §3) with this target D*, S₀, and marker q to
choose μ=17r, t>√β, so that f(μ)/D* is a square in every finite
completion in S₀ and v_q(f(μ))=1. The lemma prescribes finitely many
open congruences, hence r can be chosen arbitrarily large to avoid t=s.
For clarity: at a split unit prime a simple root of r²−m/17 prescribes
valuation parity and leading residue; at an inert unit prime the target
has even valuation and the smooth genus-one finite-field quartic supplies
a needed nonsquare unit; at 2,3,17 and p|m the prepared target and the
chosen seed are local squares. At q the other numerator factor and the
denominator are units. Its hypotheses are unchanged: if β is a square
mod q so is m/17=β/17². No global representation of D* is used.

Therefore D₀/D* is a local square at each finite p in S₀. At q the
valuation of D₀ is odd because e_s is a unit, whereas D* is a unit.
The two global classes differ. Above, v_q(f(μ))=1; the additional
square factor need not preserve valuation one. Further fresh markers
can exclude any previous finite list of complementary classes.

Use the conic C X²+D₀ Z²=1, C=b₀/17=1−D₀ with base (1,1). At every
finite p in S₀ set X*=−|v/w| (the same *rational* negative value);
pick a local Z_p with Z_p²=D*/D₀. At infinity choose the corresponding
real conic point if approximating b*, or X*=−√(b_target/b₀) for an
independently chosen 0<b_target<17. All X* differ from 1. Secant slopes
(Z_p−1)/(X*−1) exist. The rational parametrization is

    X=(D₀ L²−2D₀ L−C)/(C+D₀ L²),        Z=1+L(X−1).

At the chosen finite slopes its denominator cannot vanish: substituting
the line in the conic would then force C+D₀ L=0, and these equalities
would imply C+C²/D₀=C/D₀=0. Rational weak approximation of L (ordinary
CRT after clearing fixed local denominators, with arbitrarily small real
mesh) yields b=b₀X² arbitrarily close at all places, both ordinates
by transport, and complement D₀Z² retaining all marked classes.
Keep XZ≠0 by closeness. At each p|m, b* has positive odd valuation
since its reduced denominator is square, hence v_p(b)≥0 once close;
outside them all valuations of m(wX)² are even. This proves the square
reduced denominator. It also preserves the target depths whenever
requested. For existence at prescribed m without any preexisting target,
one may take b*=m(2²·3·17/N)² with sufficiently large N coprime to
102m. This has exact depths (4,2,2). Choosing the real target
independently gives density on the whole open interval at those depths.

## 4. Reconstructible examples and scope

The standalone verifier reconstructs four complete rational witnesses
from the short parameters in FINITE-REPLAY.json using exact fractions.
It checks both original equations before and after transport, nonzero
ordinates, exact depths, a square reduced denominator, marked complement,
and first-class identity. The examples use m=1, 9145, the literal scalar
class 12036405179807305 at input zero, and the 194-digit squarefree
five-prime product from SHARED-CLEARING-ROW.json in the independently
prime-certified linked-row packet. Its first class is that of a concrete
original-model row, not a proof of full fifteen-position Values. The
actual scalar polynomial integerR(0)=4376874610839020 satisfies
11 integerR(0)=4m; the scalar of the original construction still has
a specific normalization and complement which are not recovered here.
The output digest binds b,E,S,y₁,y₂ in that order, as five reduced
numerator/denominator lines. No probable-prime or search assertion
enters verification of the pair identities.
