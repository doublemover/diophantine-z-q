# The actual universal family and one unsplit finite KS comparison

## The selected family, not another surface with the same t

Fix the actual marked D=210 point from the literal 318/326 tables, rational
t=32u/v, with the same four root constants, ordering and chosen
geometric mark. Choose full levels 3 and 11 by adjoining torsion of this
same surface to the height field L. At a finite place w take the
Yuan fine level n=3 if w(3)=1, else n=11, exactly as in
the already audited two-fine-level overlap. Write X_n for this fine
scheme and pi_n:A_n -> X_n for the actual universal
family of QM surfaces with their canonical principal polarizations.
The universal family and properness are supplied by
[Yuan v2, §2.1](https://arxiv.org/pdf/2205.11334#page=5).
The two generic points are the projections of the same full-level-33
point over L; the comparison is over the moduli **stack**, not the
coarse fiber product. An unmarked coarse lift cannot replace this.

The native SelectedActualFineUniversalFamily318 is a direct pullback
producer. For the actual proper extension y:Spec O_w -> X_n already
chosen by properTrait it makes A_y=Spec O_w ×_(X_n) A_n. Its generic
fiber is canonically Spec L ×_(X_n) A_n along the very same original
x, via the upper triangle y|_L=x, and hence the selected A/L via the
classifying isomorphism. Both comparison projections and the identity
section commute. The classifying isomorphism is what is supplied by
the actual marked point, not an additional well-chosen generic
abelian surface. Base change of smooth proper group schemes is
classical. An abelian scheme over this valuation ring is the good
Néron model of its own generic fiber, so this family computes the
stable Hodge line of A at this place. This last fact is not a Lean
claim.

## The same KS on both levels and at a marked point

Use the cotangent connecting map of the actual family (Yuan §1 and
§3.1). On the common **characteristic-zero** level-33 refinement the
forgetful maps are étale: choosing the complementary prime-to-
characteristic level is a finite étale torsion marking. The pullbacks
of the two universal families, including their O-actions and principal
polarizations, are canonically the one universal family there. The
exact cotangent sequences identify under étale base change. Smooth
proper base change for H^0 relative differentials and H^1 O of an
abelian scheme, or the affine Čech connecting construction at a
characteristic-zero frame, commutes with this diagram. For the Čech
description take affine opens of the actual abelian fiber, lift a
section of the right term on each affine, and take the differences of
the lifts on double overlaps. Under the same pullback isomorphism
the lifts and their differences pull back, so the resulting classes
are the same. The actual relative cotangent line of the curve is
retained in this operation. One must **not** reconstruct the KS of
A/Spec L using the zero relative differentials of L over Q; that
would erase the deformation direction and is not this comparison.

More explicitly, in the ordered Hodge bases let C represent the
connecting map to the dual of the Hodge module of A-dual tensored
with the original relative cotangent line; let P represent
pullback under the polarization, from Hodge(A-dual) to Hodge(A).
Put Q=P inverse. The ordered matrix is Q-transpose times C; its
determinant is det(C)/det(P). This is the denominator arising from
moving the dual and the polarization in Yuan §1, not a second
application of the polarization. The new matrix owner verifies the
signed determinant and polynomial specialization on the **existing**
connection. This gives a single pointwise KS over L for all of the
chosen traits, and the same comparison at all archimedean embeddings.
No map of the full modular function field to L is used; only the
proper stalk evaluation from the previous two-module packet.

## Exact division in the original stalk

A stronger and smaller finite comparison now uses [Yuan v2,
Theorem 1.1](https://arxiv.org/pdf/2205.11334#page=3) itself, not a
pointwise choice of split-order frames. At the actual fine stalk R
let U=det Hodge(A_n) and W be the relative dualizing line of X_n.
The genuine Psi: U^tensor2 -> W^tensor2 is injective with
image exactly 210 W^tensor2 on the original regular integral
model. In particular, this statement is true before evaluation at
a possibly ramified O_w, even when its closed point lies at a
node. The resultant KS over O_w is the pullback of this map, not a
new commutant or tangent space computed over the height trait.

The new divideIso constructs Psi_0=Psi/210 as a **linear
isomorphism in the original stalk**, from the exact image and
injectivity. There is no inversion of 210 in R, no split
unramified auxiliary frame, no p times unit determinant
input, and no choice of which frame of the dualizing square to
compare with a separate rational basis. Its inverse can be applied to
each true integral tensor s of the dualizing square prior to specializing.

Fix one nonzero rational frame of the Hodge line of the original
A/L. If a primitive generator of U evaluates in that frame
to h, the coefficient of Psi_0^{-1}(s) in the square of that
same primitive generator is a_s in R. The source builds the square
maps via iota tensor iota followed by ordinary multiplication, not
by supplying an unrelated frame of the square. Specialization of
the original morphism yields the exact equality

    210 KS^{-1}(s|_L) = ev(a_s) h^2 .

Here w(ev(a_s)) <= 1 is automatic because the actual arithmetic germ
was evaluated into O_w. The identity just proved gives the finite
bound using w(h)||H||_w=1, the Néron metric in its integral
frame. In particular specialization need not be injective on R or
on its rank-one modules. The choice of an integral frame of U has
no effect on the identity: replacing it by xi times the frame
multiplies h by ev(xi) and multiplies a_s by xi^(-2).
The finite bound therefore consumes neither the old hPrim,
hDim, changeFrame, nor actualKS scalar row.

The terminal SelectedOriginalCanonicalFiniteKS318 calls the same
chosen proper-closed stalk to produce the two original integral
arithmetic tensors. Their K-classes are exactly the previous
differential numerator/polynomial fractions, and their same marked
ratio is 32u/v after evaluation (as an equality, allowed to vanish
at this stage). The finite norm bound is proved for these literal
tensors. In the archived +120 bound the archimedean term still
uses the unscaled KS, so 210 occurs exactly once on each
section; this packet neither modifies nor reproves the independent
complex metric and strict thresholds.

## Boundary of this native step

The source explicitly consumes the real fine universal family as a
scheme morphism, its classifying isomorphism, and the actual stalk
map of line modules whose image is supplied by Yuan Theorem 1.1.
It produces the actual proper-trait family, the generic same-object
identification, the divided isomorphism and the finite evaluation
inequality, not an interface assuming the final inequality.
Functoriality of the geometric cotangent connecting map, the
principal polarization and polarized Hodge/Néron metric still have
classical proofs as above. Neither the moduli representability nor
the cohomology/base change and deformation theorem has been
formalized here. A full native consumer must link the two
point-specialized tensors to the archived global chart metric at
each embedding, with the same ordered determinant, not independently
choose frames. X_1(M) compactification and its Abel columns
remain a separate lane on the modular Jacobian J.

For next hosted granularity, preserve the reviewed trait slice
bf32d656 unchanged. The new SelectedActualFineUniversalFamily318
and SelectedYuanOrderedPolarizedMatrix318 can be taken separately,
then SelectedYuanActualScaledKS318; the terminal consumes the
proper-trait/stalk and scaled KS inputs, not the matrix replay.
No local Lean build, remote writes or native compilation claim.

## Static arithmetic replay

    sha256sum -c SHA256SUMS
    python3 check_universal_family_ks.py | cmp - EXACT-UNIVERSAL-FAMILY-KS-CONTROLS.json

This replays 24 signed polarized matrix reductions over eight rational
places, 1080 normalized finite controls, and a rational arithmetic
example of noninjective evaluation. It does not instantiate an actual
QM point or verify the Lean kernel. From the workspace root the donor
manifests are verified by sha256sum -c on DONORS.sha256.
