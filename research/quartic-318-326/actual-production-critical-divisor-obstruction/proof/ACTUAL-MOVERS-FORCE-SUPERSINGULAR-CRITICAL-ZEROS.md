# Production obstruction to making the whole supersingular differential nowhere-zero

Keep the fixed lower semistable curve
Eflat: y²=x(x+76768)(x−407) and its actual
weight-two rational new differential f_N
on X₀(N), N=205042530. Keep the precise
original same-scale and parallel all-fresh
mover phases. This shows a forced **some**
supersingular zero at each actual mover,
not that a specific proposed anchor is a zero
or that there exist no nonzero anchors.

## 1. All the guaranteed Atkin-forced CM fields

Write N=2·3·5·7·11·37·2399 and let d>1
divide N. Moduli points are marked pairs (E,C_N).
At an actual characteristic-zero fixed point
of the Atkin–Lehner involution w_d, factor
its fixed isomorphism after E→E/C_d to get
an actual endomorphism γ:E→E of degree d.
The marked dual subgroup is the image of
E[d], so γ maps E[d] onto C_d and γ²
kills E[d]. Its degree is d², hence
γ²=[d] times an automorphism of E.
This automorphism preserves C_d because
it commutes with γ in the characteristic-zero
endomorphism ring; it preserves C_(N/d)
because [d] is a unit on that group.
There are no automorphisms of this full
marked pair beyond ±1: a nontrivial
cubic automorphism cannot fix a line in
E[2], and an order-four one cannot fix a
line in E[3]. The positive sign γ²=[d]
is impossible because d is nonsquare and
the endomorphism algebra is either Q
or an imaginary quadratic field. Thus
γ²=[−d]. In particular its CM field
is exactly Q(√−d), regardless of the
order discriminant within that field.

The fixed locus is nonempty if and only
if −d is a square mod every odd q|N/d.
Necessity uses the marked stable line in
E[q], with characteristic polynomial
X²+d for γ. Sufficiency: take a complex
CM curve with endomorphism √−d and
order Z[√−d]. Its degree-d kernel is
cyclic since d is squarefree; take it as
C_d. At each odd q|N/d choose an eigenline
by the indicated square condition. At
q=2|N/d the polynomial has a repeated
root and always has a stable line;
there is no extra split condition there.
Then γ(E[d])=C_d and γ preserves the
other marks, so this is an actual fixed
point. This argument proves the set of
possible quadratic CM fields from this
source, not the number of geometric
points on any one fixed locus.

For the fixed lower Eflat, the local a_q
in the displayed factor order of N are

    (+1, −1, −1, +1, −1, +1, −1).

For squarefree level the w_q eigenvalues
of f_N are −a_q; products give the signs
of w_d. A nontrivial involution's derivative
at its fixed point is −1 in characteristic
different from 2. Hence at a w_d fixed point,
eigenvalue +1 forces the differential to
be zero (eigenvalue −1 alone does not).
The exact donor for the conductor and
split table is the lower semistable source
`high-hom-1120/heegner-compressed-trace/
joined-semistsable-genus2207-r1/
ONE-RAMIFIED-LEVEL-HEEGNER-DETECTOR-ON-THE-LOWER-BASE.md`.
All divisors, Euler tests and signs are
replayed in the attached exact JSON:
21 nontrivial involutions have fixed
points, and precisely the following
13 involutions give forced zero fields
by this criterion (list the positive d):

    770, 1295, 2310, 3885, 369446, 395835, 621341,
    1952786, 2662890, 9320115, 29291790, 34173755, 102521265.

These are all **Atkin-forced** fields,
not an enumeration of all CM zeros of
the differential.

## 2. Why neither actual mover branch can make all zeros ordinary

In the historical branch p_a=415721 and
q_a have the same signed phases at B;
both b movers take the phases of
p_b=9807649. The b₂ variation detaches
11 and 2399 only from the order layers
and **preserves their rational norm signs**.
The all-fresh branch allocates new rays
to meet the same 16 old unit conditions
but its a₁,a₂ retain the p_a phases and
both b₁,b₂ retain the p_b phases on B.
These are exact retained input statements
from the two same-scale proofs, not the
false assertion that an individual mover
is a square at every p|B merely because
the product a or b is square there.
All movers are 1 modulo 8. In the same
prime order of N their two explicitly
replayed Legendre columns are

    a type: (+,−,+,−,+,+,+),
    b type: (+,+,+,−,+,−,+).

Both of the critical field signs for
d=770 are therefore −. The four
d with that behavior in the table are

    770, 369446, 2662890, 29291790.

The shortest explicit check is
d=770=2·5·7·11: w₂w₅w₇w₁₁ has sign
(−)(+)(−)(+)=+, and −770 has
square roots 1, 9, 1066 at its
remaining odd primes 3,37,2399.
Any corresponding CM fixed point
reduces supersingular when p is
inert in Q(√−770) (the classical
CM reduction criterion). That is
every actual mover under both
sets of retained phases. We have
not counted the four rows as four
distinct reductions, since collisions
are possible.

The reduction conclusion does not
need to discard the historical mover
p_a by an unknown spread-out set.
Every actual mover is prime to 2N and
to d. The compactified tame modular
curve has good reduction there,
CM elliptic curves have potentially
good reduction, and the prime-to-p
cyclic marks extend étale over a
suitable local extension. Thus a
fixed CM point reduces to a genuine
noncuspidal fixed pair at p. The
involution persists and is nonidentity:
w_d takes the infinity cusp to a
different labeled cusp on the
squarefree model, and these cusp
sections are disjoint at p not
dividing N. Over odd characteristic
its derivative is still −1 at a
fixed point. The integral newform
has a₁=1 in its reduction and
the exact same eigenvalue +1, so
its reduction vanishes at this
supersingular point **at each
actual mover**. This blocks the
proposal to make all values
automatically nonzero by choosing
movers where all critical pairs
reduce ordinary. It gives no
coefficient vanishing at a nominated
nonfixed anchor. In particular it
does not rule out a specific actual
sparse positive certificate.

## 3. The non-CM critical points do not force a new finite-cap clash

This general complementary statement
is only about adjoining a finite
Chebotarev condition; it does not
whitewash the forced CM rows above.
An exact old finite Galois cap
with prescribed conjugacy representative
can be refined to give ordinary
reduction for every fixed non-CM
critical moduli point. One need
not demand that their fields of
definition split. Here is a proof.

Choose a finite Galois K₀ over Q
where all finitely many critical
points, underlying elliptic models
and isogenies between geometrically
isogenous conjugate models are
defined. Use one elliptic model
from each geometric non-CM isogeny
class. Fix the old cap field F and
extend its prescribed element to
g₀ over K₀F. Let D₀ be its finite
order. For every sufficiently large
auxiliary prime l, fixing K₀F still
allows the independent product of
SL₂(F_l) actions on the l-torsion
of these distinct non-CM isogeny
classes. This is the adelic product
open-image theorem, e.g.
[Lombardo, Theorem 1.1](https://arxiv.org/pdf/1501.04600);
use it over the fixed number field
K₀F, not a claim of disjointness of
the critical point fields from F.
The single-factor case is Serre.
Exclude l dividing the finitely many
chosen isogeny degrees.

The full Galois action permutes
these geometric classes. On the
disjoint projective l-torsion
spaces it gives the corresponding
permuting projective action:
isogenies identifying two non-CM
models in the same geometric
class are proportional in
Hom⊗Q (that space has rank one),
so their projective identification
is independent of the chosen
isogenies for these l. Composition
has the same property. For a
cycle of length d|D₀, alter the lift
of g₀ by an independent SL₂ element
only on one class of that cycle.
The cycle product can then be
any element of its PGL₂ coset
modulo PSL₂. Choose a split diagonal
element with projective eigenratio
a primitive square, or a primitive
nonsquare, matching that coset.
Its projective order is at least
(l−1)/2. The factor D₀/d of
taking g₀'s full return reduces
order by at most D₀. With
(l−1)/2>6D₀ the resulting full
return has projective order >6
on every represented class.
The choices for different cycles
are independent, and all fix the
exact old cap F.

Why this certifies ordinary reduction:
if an elliptic curve over F_(p^D₀)
is supersingular, its Frobenius
eigenratio has finite order ≤6.
Indeed π²/p^D₀ for an eigenvalue
π is an algebraic unit with all
complex conjugates of absolute
value 1 by the supersingular
slope 1/2 and the Weil bounds;
it is a root of unity in a
field of degree at most 2.
The two eigenvalues' ratio is
that unit. Frobenius is semisimple
as an elliptic endomorphism,
so a power with exponent ≤6
is an actual scalar, and its
mod-l projective order divides
the same exponent. There is no
unipotent exception from reducing
the eigenvalues. Therefore the
prescribed long projective order
excludes supersingularity. Good
reduction at the varying prime
outside fixed bad primes is
understood. Chebotarev realizing
the refined finite element then
does what is claimed. Critical
CM points, instead, become
ordinary precisely on splitting
in their CM fields, and those
quadratic conditions can clash
as in §2.

This last argument concerns the
finite cap. If using it in a full
prime-order construction with an
infinite Gaussian gcd tail, the
new finite torsion extension and
its ramified primes must be
incorporated before repeating
the tail argument with the
refined positive density. No
unverified simultaneous inherited
gcd-tail statement is being used
for the obstruction above.

Replay, standard Python:

    python3 -B check_actual_atkin_forced_critical.py | cmp - EXACT-ACTUAL-FORCED-CRITICAL.json
    sha256sum -c SHA256SUMS
