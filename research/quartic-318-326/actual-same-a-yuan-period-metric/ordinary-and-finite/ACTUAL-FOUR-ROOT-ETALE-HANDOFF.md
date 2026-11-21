# Étaleness of the literal four-root t-chart at the actual fine point

Fix the original D=210 arithmetic normalization of the curve and
its four ordered root coordinates. On the noncontact affine open
its coordinate ring is the existing ContactKummerOrder318.OpenOrder
for c=(-14,-6,42,-21), and the four contacts are (0,32,76832,-343).
The chart is not recalculated from geometric signs. The original
full four-root rank-sixteen finite-free étale theorem is already
available as ContactKummerOrder318.open_finite_free_etale.
The current packets do not replace it with a new four-root scheme.

## Same actual ring map, all four ordered roots

Use the exact selected proper local point of either fine level.
Let B=A_P be its marked characteristic-zero localization, with the
genuine field point B -> L constructed earlier, and t its actual
germ of the original t variable with value q=32u/v. The point is
off all four finite contact values and infinity. Each t-b_i has
nonzero field value and so is a unit of B by the previous field-value
localization theorem. It is not asserted to be a unit at the closed
arithmetic point. Their product forces the literal map from Q[T] to
B to factor uniquely through the actual OpenBase. This is the same
away denominator as in the original four-root chart.

Let y_i be the pulled-back germs of the four given coarse roots.
Their exact equations over B follow either by pulling the named
coarse coordinates through the actual forgetful map or by the
explicit chosen arithmetic chart identification at the mark.
The map OpenOrder -> B is *constructed* from all four equations by
four AdjoinRoot lifts over the chosen OpenBase and tensoring in the
archived order. It sends t and each root to those exact germs.
Conversely an OpenBase-linear comparison taking all four generators
to those germs is equal to this one: use the two tensor extensionality
layers and each AdjoinRoot root generator. Thus the equalities used
to identify this map with the actual PEL pullback cannot be faked by
sharing only the value of t. Where compatible field evaluation
needs checking, the roots read at L are those pulled through the
fixed original marked point field P -> L (the same earlier mark).

The ordinary chart is formally étale over the original polynomial
axis because the base away-localization is formally étale and its
four-root finite-free cover is étale. The alternate one-variable
MvPolynomial presentation is explicitly identified with the
existing polynomial t by uniqueAlgEquiv and its action on X.
The new Lean lemma composes the actual coarse-to-fine ring map
with these two certified components, and rewrites by equality on
the literal polynomial generator. In particular
formal_axis_at_nominated_point does **not** assume formally étale
for this composite. Its sole remaining geometric comparison is
formally étale of the actually constructed relative
OpenOrder -> B ring map.

## Why the remaining relative étaleness holds, classically

The actual geometric maximal **stack** of QM D=210 abelian surfaces
has only the central automorphisms ±1 in characteristic zero,
including special CM points. Indeed over the complex numbers its
rational H_1 is a left module of dimension one over the division
quaternion algebra of dimension four over Q. Its B-linear
centralizer on H_1 is the opposite quaternion algebra. A
polarization-preserving automorphism has finite order, and its
faithful rational homology matrix comes from this centralizer.
An element of a quaternion algebra satisfies a quadratic polynomial
over Q; its possible nontrivial roots of unity besides ±1 require
Q(i) or Q(sqrt(-3)). The former splits at 5 and the latter at 7
(because -1=2^2 mod5 and -3=2^2 mod7). A split quadratic algebra
cannot embed into the local division algebra at that prime:
its nontrivial idempotent would survive. Consequently the
relative inertia is precisely the canonical sign group.

The sign action is a natural central subgroup functor, so the
actual maximal stack rigidifies by it. [Abramovich–Corti–Vistoli,
Theorem 5.1.5](https://arxiv.org/pdf/math/0106211#page=16) gives
an étale rigidification with the same coarse space; no stabilizers
remain, so its algebraic space is that coarse curve itself. The
legitimate stack gerbe is not replaced by a product of independent
coarse lifts. The full fine-level forgetful map to the maximal
stack is finite étale in characteristic zero because its fibers
are full ordered O-linear markings of the finite étale torsion
of the given family. This uses the genuine moduli schemes and
representability in [Yuan, §2.1](https://arxiv.org/pdf/2205.11334#page=5).
Their composite to the coarse maximal curve is étale.

Restrict this composite to the same actual ordinary chart and
the selected fine generic point, then pass to its local ring B.
Localizing an étale algebra gives a formally étale algebra;
finite presentation of the whole local stalk is neither
claimed nor needed. This proves the classical premise exactly
for the constructed OpenOrder -> B. It uses representability/
identification of the genuine moduli spaces and their selected
labels, not any hypothesis that t itself was formally étale
on the fine model. This justification stays in characteristic
zero and implies no analogous coarse comparison on the bad
reduced fibers at 2,3,5,7.

## Minimal hosted source

SelectedLiteralFourRootEtaleAxis318 contains the exact two-step
original coarse proof and ring hom composition. This is the
smallest new target; the primitive dt owner eec6c707 and cached
original noncontact chart are its donors. The second file constructs
the ordered root pullback, requiring no separate denominator
witness for the selected point. No model representability, stack
rigidification, or full PEL comparison is proved by Lean here.
The remaining separate geometry for actual KS is the genuine
polarized cohomological construction and base change. No Lean
build or remote write.

    sha256sum -c SHA256SUMS
    python3 check_literal_coarse.py | cmp - EXACT-LITERAL-COARSE.json
