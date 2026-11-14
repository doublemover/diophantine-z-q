# Original whole-overlap specialization repair (source-only)

Basis: hosted Lean run 43534276453, head a2d615a4183174328321ea21d60879add229de3a, positive packet contact-original-positive-generators-r66, artifact 14089072985. OriginalTensorChartWholeRestriction318 passed (18.915 s); ContactOriginalWholeRestriction318 first failed (3.976 s). Exact log is retained in ../positive-logs/progress-experiments/contact-original-positive-generators-r66/logs/ContactOriginalWholeRestriction318.log.

## Bound source

Before ContactOriginalWholeRestriction318.lean SHA-256 fd32d2d280e0d291696dd04f8975da132a2cf0656a9b185fc5ddf33aab7b2422. Candidate SHA-256 619d6667786ed04c54d15216d55c7e013e7f3e8250291343a3db5561d80984d8. The generic producer is the unchanged OriginalTensorChartWholeRestriction318.original_restriction at the same commit; its proof passed this hosted run. Its required source definitions are ContactOriginalRestrictionCoordinates318.finiteRestriction/infinityRestriction, ContactWholeOpenSectionRestriction318.finiteDirect/infinityDirect and OriginalOpenPullbackSections318.sectionPull. The exact producer and definitions remain in the immutable predecessor folder.

## Required versus constructed inputs

The producer quantifies R,A,B:CommRingCat with both R-algebras, an original scheme X, p:X→Spec A, j:X→Spec B, i:Spec(A⊗R B)≅X, equalities i.hom≫p=Spec.map(leftMap) and i.hom≫j=Spec.map(rightMap), an original line L on Spec B, a module M on X, e:j*L.object≅M, and every full-open section s of L.object.

Both applications now specify every parameter, in the producer's actual order. R is Polynomial ℚ, A is OriginalLaurentProjectiveOverlap318.Ring; B is respectively ContactKummerOrder318.SourceOrder c or ContactWholeInfinityAlgebra318.Ring c. p is projection c; j is finiteEdge c or infinityEdge c; i is the same original tensor chart finiteIso.symm or infinityIso.symm. The same inv_base and inv_chart proofs discharge the exact equalities. The lines remain finiteLine c L and infinityLine c L; M remains the object of ContactOriginalLineOverlap318.line c L; e remains its finiteComparison or infinityComparison. The section is the original arbitrary m. The reciprocal application retains the existing infinityHom.toAlgebra instance, with u↦T⁻¹ action, not the finite action.

Narrow import-all directives make the two original restriction definitions and direct-section definitions available for explicit dsimp only. No replacement chart, chosen basis, alternate recovery, reduced open, restriction of the quantified section domain, or changed ring is introduced. The original adjunction unit's sectionPull is exposed in its producer; the source definition uses moduleSpecΓFunctor.map of that identical unit.

## Bounded transport route

The log's last error is the concrete infinity_square change at the default 200000 heartbeat limit. Both finite_square and infinity_square retain their original public statements. The private image_restriction helper proves, for any scheme/module and U=V with U≤W and V≤W, that mapIso(eqToIso(h.symm)).op applied to restriction W→U is the original restriction W→V. The direction of h.symm and op is exactly overlapEquiv's direction. Its proof compares generic concrete presheaf maps and composes them with Functor.map_comp_apply; the final morphisms agree because open-set categories are thin. Every input section of Γ(M,W) is covered.

The concrete uses retain overlap_image c : (into c) ''ᵁ ⊤ = finiteOpen c ⊓ infinityOpen c. They apply the already proved ContactWholeOpenSectionRestriction318 finite/infinity square before this helper, keeping its original image inclusion and the same inf_le_left/inf_le_right target. Thus the result is the identical section of the same original ambient intersection, not a related chart or isomorphic substitute. Explicit dsimp only on overlapEquiv/AddEquiv.trans_apply avoids the previous large concrete change.

## Consumer and verification limits

Consumers remain the whole-original restriction square, hence downstream original Mayer–Vietoris/cohomology/positive-twist arguments. No producer proof, downstream source, theorem statement, resource cap, or acceptance verdict is changed. Exact imports are extended only to expose source definitions for the explicit proof. The helper adds no assumptions to a public theorem.

No Lean, Lake, kernel, or full arithmetic verification has run locally. This is a source-level repair candidate; successful elaboration of exact instance/coercion endpoints and bounded runtime still require hosted Lean. Independent source review must bind this candidate and contract before packaging, then propagation must be reviewed separately.
