# Independent source review of six replay repairs

Reviewer: /root/advance_period_models. Author: /root/reconcile_proof_queue. Date: 2026-11-11.

Scope: source-level comparison against exact hosted predecessor errors from commit 31a0e67e2709e0ff84b00591b071f292c6207eed, replay 42838588630. No local Lean execution. These findings do not claim successor compilation or new mathematical acceptance.

## Result

Five successors are acceptable as bounded elaboration repairs, subject to hosted replay: height-original-metric-assembly-r47, height-normalized-valuative-center-r39, original-five-pointed-norm-decomposition-r36, original-finite-quotient-reconstruction-r29, and contact-original-positive-generators-r38. source-hone-original-norm-matrices-r31 remains incomplete at the reviewed bytes.

## Exact comparisons

- IntegralWholeOrderOpenMaps318: the reported RingHom universe mismatch is resolved at its source by using a common universe for A and T before forming CommRingCat/Spec. This narrows the otherwise ill-typed generic declaration to its required common category universe. The actual polynomial and Laurent carriers already have that common universe. The coefficient maps, localization parameter, tensor inclusion, source and target are unchanged.
- ThreeRootScaledGenerators318: simp replaces simp only in the individual generator calculation. The same literal tensor-root generators, signed unit scaling and all three indices remain. The old errors retain unevaluated vector applications; broader definitional simplification is a plausible repair, not verified compilation. Parameter transport and the downstream generator consumer are unchanged.
- DualNumberScalarExtension318: the universal lift requires Commute, as verified in the pinned primary DualNumber source. Commute.all supplies that property in the same commutative tensor algebra. Explicit epsilon carrier annotations preserve the original epsilon in DualNumber S versus DualNumber R. The two inverse algebra maps, actual scalar extension, augmentation and kernel ideal remain the same.
- OriginalNormalClosureGalois318: importing RatFunc.Basic supplies the genuine polynomial fraction-ring implementation missing in the error log. Explicit R/S/A tower parameters match the pinned of_algebraMap_eq statement and the already defined composite scalar structure. Explicit faithfulSMul arguments fix a partially applied equivalence. Neither the integral-closure carrier nor the full original Galois action, coefficient square or residue field quantifiers changes.
- LaurentVectorFiltration318 and LaurentTransitionBounds318: expose permits downstream span induction on the same original filtration, precisely matching the hidden-definition error. The explicit Finset sup function fixes inference, and the expanded reflexivity proof is literally membership in Iic. All Laurent columns, transition maps and negative-tail quantifiers are retained.
- InfinityBasisUnitCoefficients318: adding Fin.cases addresses residual ratio indices but not the separate basis_square all-zero error `1 = 1 tensor 1`. The zero case needs the actual tensor-one identity. The i=0 ratio product also has opposite parenthesization, requiring associativity after index reduction. The current patch is therefore not accepted as a complete repair. Neither issue requires changing a theorem statement.

I read the changed declarations and surrounding consumers, predecessor diffs and exact failure logs. Primary files checked include DualNumber.lean, Tower.lean, RatFuncBasic.lean and RatFuncDefs.lean in build/reconcile-repairs/primary. No historical manuscript/application acceptance is refreshed. The independent review is internal model review, not whole-proof validation.

## Follow-up binding

The author added `Algebra.TensorProduct.one_def` to the unchanged all-zero basis-square proof and `mul_assoc` to the same full ratio-product proof. I re-read these exact changes. Both previously identified missing simplifications are now present and retain the statement, coefficient twists and original basis. The source-hone r31 successor is now also accepted as a bounded source-level repair, subject to hosted replay. This is an approval of the updated source bytes, not of any future revision or of successful compilation.

## Provenance follow-up

I reviewed the six current APPLICATION recovery_delta fields and current intake/copy hashes, verified each current source hash, and compared every unchanged Lean file against its immediate predecessor. The previously reviewed modified Lean bytes are unchanged. The immediate-predecessor COPY_BINDINGS and current metadata hashes are recorded separately in REPAIR-REVIEW-bindings.json. Copied historical evidence is retained rather than re-authorized by the source repair. This metadata refresh does not turn the source review into hosted compilation or whole-proof approval.
