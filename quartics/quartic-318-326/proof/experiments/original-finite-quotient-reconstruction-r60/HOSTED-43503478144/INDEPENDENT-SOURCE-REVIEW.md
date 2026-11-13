# Independent Picard source review for run 43503478144

Reviewer: lean_review_resume, separate from repair author. Scope: three successor packets against head 56773da3e1a8045d885059ae17053fcbf0af6067 and exact predecessor hosted diagnostics. No local Lean/Lake execution, push, acceptance refresh or theorem-completion claim.

## Bound final sources and packet scope
- contact-relative-site-descent-r74: ActualAffineEffectiveComparison318.lean SHA256 b591ea84f9867aa371c401904a788bff3337802e73d388897694d95d1baf9ed8. Exactly one changed root Lean file; other 286 unchanged. APPLICATION.json d234dec0dd892262f703e9dfbb5bd61f6c269ff19d0c54d3bad1a18ee6139b1c.
- original-finite-quotient-reconstruction-r60: OriginalCartesianNormalChart318.lean SHA256 23cec616231beacad2d0ce7147ce2a29102feac6fb9ca10420a4eb9834e86e86; OriginalCartesianChartCoefficients318.lean SHA256 e07d7507e6f733794bd5bf9b6430fc58a67cb84ba13107e9c03fcdd0f140e154. Exactly two changed root Lean files; other 78 unchanged. APPLICATION.json 611a6ef47f8ddf42ef74ae9788fcbbd772e41697806f98a701b3b5d07589ea18.
- relative-original-normalized-kernel-gluing-r4: OriginalAffineLinePathSections318.lean SHA256 f1f6da03eb0fb200c1034d75ac218d6ddb5687f4f770b6c8168bdf33313c2940. Exactly one changed root Lean file; other 1297 unchanged. APPLICATION.json 6dc949dfcd78ef2f80f3b6f6e3de9b5ae45644139e748a0ac49bafb0694cb2dd.

For each successor, independently checked identical root Lean filename set and ordered intake modules against its predecessor, exact changed-source hashes, all APPLICATION source/artifact bindings, and predecessor intake SHA256 equality to hosted RESULT.packet_sha256. No new modules or changed solver options. No statement of static success here substitutes for hosted elaboration.

## 1. Affine effective comparison
Exact diagnostic log SHA256 56de5dee2f16afb54be4af3a11c89bdf9c352502af42ca0bdb1e944393fa0526 reports transport rewrite missing because the target contains doubleIso.symm.hom, and later simplification retaining the functor image of an identity behind a concrete limit carrier.

The repair first normalizes Iso.symm_hom and explicitly specializes the existing ActualCanonicalOverlap318.transport at R, S, and the same named descended module M. It does not replace the reconstructed module, either overlap map, the original input tau, or the reflecting scheme isomorphism.

The new private conjugation_commutes is ordinary categorical cancellation: compose on the left by P.map e.hom, combine its composition with P.map e.inv, then apply hom_inv_id, Functor.map_id and id_comp. It is proved on generic categories before specializing to the large actual nerve carrier. Its use in comparison_commutes preserves both original pullback functors, the actual reconstruction comparison, and the original overlap compatibility square. The final effective theorem still takes only the original geometric diagonal/cocycle laws. No abstract descent compatibility premise is added.

## 2. Cartesian normal chart and producer visibility
Exact diagnostic log SHA256 d16f345039886472e71f4cbbe9a4e66b5a9805e1fa1ac837d74d4341c6bcd1a8 reports unsynthesizable hidden p/j/f parameters in local instance registrations, then missing algebra/module/tower instances and cascading public-call errors.

The named quotient/chart/coefficient actions retain the exact previous bodies. FiniteDimensional and IsGalois binders are explicitly scoped under quotientAlgebra p, not under a newly assumed arbitrary field action. Each public type/body installs that same action and the necessary finite/Galois evidence. The chart action is ActualOpenFractionField318.sourceAlgebra j and the coefficient action is f.toAlgebra. Tower and integrality remain derived from the actual Cartesian square H through the producer, and fraction-field status comes from the actual original open chart j. No scalar-tower, integral-closure, fraction-field or field-comparison premise is added to the public user inputs.

Read OriginalNormalClosureGalois318.baseAlgebra, OriginalSchemeDeckFieldAction318.baseAlgebra, the producer actions/tower/integrality, and OriginalNormalSectionClosure318.equivalence/equivalence_embedding. Under the named quotient action, the native polynomial action reduces to ((DominantFunctionField318.map p).hom.comp kappa).comp (algebraMap Polynomial (RatFunc Q)), converted by toAlgebra: exactly the producer polynomialAlgebra p. The two chart actions both reduce to sourceAlgebra j, and both coefficient actions to f.toAlgebra. Thus the intended compatibility is definitional, not a mathematical assumption.

The final producer delta adds expose only to polynomialAlgebra, chartAlgebra and coefficientAlgebra, without changing bodies. Pinned LeanMutualDef.lean finishElab lines 1343-1352 confirms an ordinary instance_reducible def is not auto-exposed merely by that attribute; this resolves the identified cross-module transparency risk. The producer quotientAlgebra is not used by these returned tower/integrality types and is unchanged.

The public sections/specIso/chart and fraction_chart/chart_base/point_chart/point_coefficient retain the original intended carriers/maps/equalities. The last point arguments move under leading scoped lets, preserving their explicit application arity after reduction. Read the immediate consumer OriginalCartesianCurveReconstruction318: it supplies the identical quotient field action and field_structure proofs; its uses of sections/chart/point_chart/point_coefficient and reconstruction compatibility remain semantically aligned. Since the old declarations did not elaborate, this is preservation of intended formulas and hypotheses, not comparison to nonexistent successful old elaborated terms.

Checked pinned Mathlib Tactic/CategoryTheory/Reassoc.lean at commit 56a005855ea17e0b0958f73ec801ae140b0a1679, GitHub blob 6523c3e000904fe821fe3566aeee0fe8d16ccbf0. reassocExpr uses forallTelescopeReducing before its equality handler; that handler matches by assignIfDefEq. Leading letI result types therefore do not present a structural reassoc-attribute obstruction. This remains a source-level API check, not an execution of generated lemmas. Source URL: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Tactic/CategoryTheory/Reassoc.lean

## 3. Original affine path restriction
Exact diagnostic log SHA256 6693a604956fca54c6d6c473ddc9c25b2a2421f615283415708dbca3d8339a1c is the failure in OriginalAffinePathWholeSections318: restriction cannot be used as a simp definition because its body is not exposed, followed by rfl retaining the opaque application.

The sole source change adds expose to OriginalAffineLinePathSections318.restriction. Its body remains exactly the actual geometric pullback unit, global-section comparison, and specified path isomorphism. Read restriction, unit_apply, restriction_smul and consumer restriction_direct. No source or target module, scalar action, top-open restriction or original map changes. The exposure directly addresses the observed imported-definition failure, not an altered mathematical restriction.

## Conclusion
No source-level blocker identified in the bound final four-source delta across three packets. The producer visibility issue was identified and corrected before this final review. These are suitable candidates for hosted strict replay only. Exact elaboration, inferred binders, generated reassociation lemmas, and complete downstream closures still require hosted Lean results. No local compile or claimed independent acceptance.
