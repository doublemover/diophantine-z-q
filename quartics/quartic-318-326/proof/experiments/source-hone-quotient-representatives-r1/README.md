# Actual target classes and original quotient pullback representatives

This82-source packet copies geometric-signs-r2 exactly and adds four modules.
No local Lean build was run. Hosted strict compilation, recursive axiom auditing
and independent acceptance remain pending for the whole chain.

MayerVietorisCoverRefinement318 proves naturality for two actual covers on the
same space when each chosen source chart is contained in the corresponding larger
chart. It constructs the actual short-complex morphism with the same ordered
difference map, applies Ext-class naturality, and proves the boundary equality on
literal restricted sections. Refinement is proved, not replaced by equality.

RefinedSchemeBoundary318 combines that refinement with the original global
scheme-pullback boundary theorem. The chosen source cover need only map into the
target charts; it need not be the whole inverse-image cover. Its representative
map is exactly f.appLE on the original overlap sections. A separate affine-square
lemma identifies actual ring coordinates under that original section map.

WeierstrassBoundaryClass318 constructs an actual H1 class for every rational short
Weierstrass scheme. The literal principal target overlap is identified with the
entire finite/infinity intersection using the original pushout overlap theorem.
Its specified representative is x_aff²/y_aff, transported by the original overlap
isomorphism. The resulting actual Mayer–Vietoris boundary is defined without
assuming it is nonzero or presuming its genus.

OriginalCharacterClassPullbacks318 proves the concrete source finite and infinity
charts refine each of the four original target covers, using the exact existing
completedMap chart factorizations. The exact sourceOpen/target overlap square is
proved with the old overlap_finite map and original chart routes. Thus the original
characterPullback of the specified target class is the actual source boundary of
an explicitly given element of the original overlap ring. Only after fixing that
ring element does the proof compute its original field image as rawX²/rawY, and
then the exact xScale²*(t-centroid)² divided by yScale*triple-root formula. Every
normalization factor is retained.

The class is not yet proved nonzero here. Computing a nonzero actual source
residue, or a uniform original target residue proof, is still required. The fifth
source finite chart does not globally lie in the target finite chart, so that case
is deliberately not inferred by analogy; it requires another refinement or the
uniform target argument. The prior original-five-sum injectivity remains, but no
unconditional exhaustion or normalized-transfer inverse is claimed in this packet.
