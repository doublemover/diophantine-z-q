# What instantiates the one-lattice modular height theorem

This is the geometric witness map for
SelectedOriginalOneLatticePeriodHeight318.original_height_from_one_lattice.
It concerns only the original modular Jacobian, not the separate
quaternionic abelian surface or its quotient comparison. The Lean
source has explicit geometric arguments; the construction described
here is a paper argument for those arguments, not a claim that the
corresponding geometry is Lean-compiled.

Fix the original level M ≥ 5. Choose the primitive chart once, by
the strict checked whole-complex-root theorem. Its polynomial p, marked
abscissa, sign involution, and j-coordinate are not changed below.
Scalar reflection proves that the full rational and the full L(J)
root algebras of that very p are fields (not selected factors). Denote
the actual rational finite normal compactification by X and its
Jacobian by J_X. The usual modular analytification is attached to X
through its actual ordinary marked-period chart, followed by unique
extension over the omitted finite fibres of the same projective line.

## Pick the common number field once

Start with the compositum of the literal j=1 splitting field of p
and any required common field for the same-A comparison. Apply
[Javanpeykar, Theorem 4.3.2](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf#page=31) to
choose a finite extension L over which the minimal regular resolution
of the finite normalization is semistable. Thus the literal j=1
splitting-field embedding into L in the theorem is its actual one,
and every selected point extends as a section by properness. No new
sample of the square minor is needed. This choice of L comes after p;
neither the arithmetic argument nor its complex embeddings change p.

Let H be the module of invariant differentials at the identity of
the Néron model of J_X over the ring of integers of L. This is finite
locally free, hence finite flat over that ring. Its generic fibre
identifies with invariant differentials of J_X. For any one of the
L-rational marked points, its Abel–Jacobi map identifies those with
the regular canonical differentials on X_L. A different base point
only translates the Jacobian and leaves invariant differentials
unchanged. Proper flat scalar extension along the field embedding
identifies these differentials with the literal base-change of the
rational global sections used in the theorem. This gives one actual
generic AJ isomorphism, not an integral equality between the entire
dualizing lattice of an auxiliary model and H.

At a finite place v the local module in the source is exactly
H_v = O_{L,v} ⊗ H. The native tensor identity recovers the very same
generic AJ and ordered coordinates on the simple tensor 1 ⊗ a.
The DVR, polynomial normality, and denominator-of-norm-one
calculation are supplied by the actual localizations. No local
differential bases, completion-norm factors, or unrelated determinant
identities are choices of the comparison.

## Why this H supplies the stated height-one trace test

Work at one v with O = O_{L,v}. Set A = O[J] and let B be its integral
closure in the original whole generic field F over L(J). For a
principal height-one prime q of A, every point of Spec B above q
has height one. Indeed finite integral extension gives incomparability,
and going-down over normal A plus injectivity on the generic field
gives the height-one assertion. The normalization is regular at these
codimension-one points; its minimal regular resolution is an
isomorphism near them. Over a horizontal prime this is on the
characteristic-zero smooth generic curve. Over a vertical prime these
points are generic points of the geometrically reduced special fibre
of the semistable regular model, and hence are smooth relative to O.

Use the whole-fibre principal-neighborhood theorem: the complement of
the smooth locus has finite closed image, which misses q. Thus there is
an s not in q such that the entire inverse image of D(s) is smooth over
O. In particular this is an actual finite-type neighborhood, not an
application of finite-type duality to the essentially finite-type
local ring A_q. Its generic point still has the whole field F.

The generic Abel–Jacobi map extends to this smooth neighborhood by the
defining Néron mapping property. Each a in H_v pulls back to an actual
regular relative differential there. Finite duality on this finite map
uses the literal finite Hom and the dualizing line of A[1/s], whose
basis is dJ. Transitivity identifies the source dualizing line with
its regular smooth differentials; at the generic field, the
identification with finite Hom is the **trace pairing**, not a freely
rescaled field pairing. See [Stacks 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
for transitivity, [Stacks 0FKW](https://stacks.math.columbia.edu/tag/0FKW)
for the affine finite Hom, and [Stacks 0BW0](https://stacks.math.columbia.edu/tag/0BW0)
for the finite trace-duality comparison. If the pullback coefficient
is a_F in a_F dJ, the resulting functional is literally
b ↦ Tr_{F/L(J)}(a_F b) dJ. Consequently all the named trace values on B
belong to A[1/s], and therefore to A_q inside L(J). These are the
exact local tests in the source. A branch field trace is never
substituted for the whole semilocal trace.

## Why the period rows give the actual stable metric

At every complex embedding, take the same ordered algebraic basis
and a symplectic homology basis of the compact curve, and write its
two matrices of periods P,Q. The constructed cusp forms agree with
the pullback of those differentials on the literal ordinary chart;
uniqueness gives them on the compactification. In the true quotient
the weight-two factor y² cancels y⁻² in the hyperbolic measure.
The conjugate-first ordered Gram G is exactly that compact integral,
including across the finite omitted set (zero area). The two
Riemann bilinear identities are
  P Qᵀ = Q Pᵀ,
  G = ((i/2)(P conjugate(Q)ᵀ − Q conjugate(P)ᵀ))ᵀ.
The native argument derives invertibility of P from precisely this
Gram's positive definiteness, rather than supplying a new basis.
The Abel–Jacobi period lattice is generated by these columns, so real
covolume is the absolute determinant of the (Re,Im) block. With the
height convention (2π)^(-g) in the squared norm, the squared norm of the
same wedge is that covolume divided by π^g. Thus the
same global invariant lattice and literal complex norm are exactly
the finite and archimedean contributions to the absolute stable
Faltings height. All embedding and field-degree averages occur once.

The resulting bound is h_F(J_X) ≤ g log(1727 M), with g ≤ M². This
still must be transported through the actual same-A quotient/isogeny
comparison before it says anything about the distinct surface A.
