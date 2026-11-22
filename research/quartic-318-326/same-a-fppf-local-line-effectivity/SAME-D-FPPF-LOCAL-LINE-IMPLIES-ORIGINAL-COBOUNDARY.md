# Local effectivity on the single original dual-number test

Let A/k be the actual original closed QM surface with the original
identity, D=k[epsilon]/(epsilon²), and Y=A×Spec(D). Use one of the two
already constructed actual directional lines L on Y, with its actual
affine frames and transition 1+epsilon f_ij on the whole original
affine intersection. Here f_ij is the original right-minus-left lift
difference. The corresponding polarized represented-dual tangent
point must designate this actual line class by the same signed
Yuan-to-directional comparison. Different line classes or the modular
Jacobian are not interchangeable.

Suppose its image in the relative Picard **sheaf** is zero. The plus
construction, applied twice if necessary, gives a covering on which
its actual line class is zero in the presheaf quotient by base lines.
After trivializing that pulled base line and refining to an affine,
choose one nonempty member Spec R→Spec D; because Spec D has just its
one point, this single flat member is surjective and hence faithfully
flat. Two lines can use separate R. Equivalently the classical
representability of the rigidified dual immediately gives an actual
trivialization over D, a stronger input than needed here.

Write d for the image of epsilon in R and C=R/(d). The given actual
local frame coefficients of a generator of L_R are units
g_i in B_i⊗_k R, where B_i is the ring of sections of the original
affine, with the exact same intersection restrictions. On the
literal base-changed overlaps in A_R, they satisfy
`(1 + f_ij ⊗ d) g_j = g_i`.
Modulo d their reductions glue to one global unit of A_C.
Since A/k is proper and geometrically integral with its k-point,
Γ(A,O)=k. Apply flat base change of *functions* to k→C (every
k-module is flat) to get Γ(A_C,O)=C, also when C is nonreduced.
The unit is therefore the actual restriction of one a∈C×.
Choose a unit lift u∈R×, using square-zero of (d), not a
ring section of R→C.

Multiplication by d descends as a linear map C→R, because d²=0.
Tensor on each genuine B_ij over k. Hence
`(1⊗d) g_j = 1⊗(d u)`; the exact full transition now gives
`g_i - g_j = f_ij ⊗ (d u)`.
As D→R is faithfully flat, d≠0; as u is a unit, d u≠0.
Choose a single k-linear functional λ:R→k with λ(d u)=1.
Contract each g_i along that same λ. Naturality along the
actual affine restrictions gives
`f_ij = b_i|_ij - b_j|_ij`
on every original overlap, with the original sign and no
choice of a new cover of A. Equivalently, the original line
is genuinely trivial; more usefully the b_i directly correct
the original directional local lifts, without formalizing a
general fpqc descent of module-isomorphisms or flat base change
of their section spaces.

This proof allows fppf tests with no lift to dual numbers over a
field. For example R=k[x]/(x⁴) with epsilon→x² is free rank two over D;
when k is a field there is no D-algebra map from R to K[epsilon]
for any field extension K/k, since an element a+b epsilon with
square epsilon would have a²=0, forcing a=0 and then its square zero.
Never assume the chosen fppf cover is étale, reduced modulo d,
a finite field extension, or splits as an algebra.

Native arithmetic owners supply the exact square-zero quotient
factorization, faithfully flat nonzero coefficient, unit lift,
single functional, and signed contraction from the supplied genuine
tensor chart values. The actual fppf local trivialization on this
line and actual chart/global-unit comparisons are **still** geometric
inputs to the native arithmetic owners; the paper derives them on
this original surface. No whole Picard representing functor or
general descent effectivity is proved in Lean here.

Primary geometry: [Stacks Sites §7.10](https://stacks.math.columbia.edu/tag/00W1),
the filtered-colimit description following Lemma 7.10.6 applied twice;
[Stacks Picard §99.11](https://stacks.math.columbia.edu/tag/0D28),
and [Lan Theorem 1.3.2.3](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf)
for the stronger actual rigidified abelian dual. Pinned native algebra:
[Mathlib vector-space extension](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Basis/VectorSpace.lean#L262-L276),
[quotient linear map](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Quotient/Basic.lean#L102-L113),
[faithfully flat detection](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean#L441-L455).
