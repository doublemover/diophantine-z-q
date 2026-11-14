# relative-original-normalized-kernel-gluing-r14

Draft successor to `relative-original-normalized-kernel-gluing-r13` at `f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb`.

## Exact hosted evidence

Run43586414080, job132422325735, artifact14110354609. ContactCoefficientSectionEquivalences318 passed in 2.418s. OriginalPullbackSquarePasting318 failed in 4.721s with three residuals: Iso.refl.hom at congr_first, pullback.map(identity) in H5, and reflexive/component-inverse projections in the final pasting comparison.

## Observed repair and connected preventive scope

Observed-frontier repair: Normalize only those observed residuals: add native Iso.refl_hom in congr_first and the final simp list, qualify CategoryTheory.Functor.map_id in H5, and use native Iso.app_inv in the final simp list. All comparison definitions, path proofs, public statements, A1–A8 objects and H1–H5 equations retain the same maps and orientation. Separately source-reviewed PREVENTIVE_UNOBSERVED connected repairs add only native Iso.refl_hom/trans_inv/refl_inv/app_hom/app_inv normalization where needed in the existing SectionPullbackComposition.path, LineSquareSections.original_square and both coefficient finite/infinity restriction-square simp lists. All original statements, full-section domains, coefficient actions and exact producer/consumer maps remain.

Preventive modules: `OriginalSectionPullbackComposition318`, `OriginalLineSquareSections318`, `ContactCoefficientRestrictionSquares318`. Each remains **PREVENTIVE_UNOBSERVED**, separately source-reviewed and never asserted to have failed in the hosted log.

## Verification

1298 root modules in the original order; 4 changed and 1294 byte-identical. No modules added/deleted; imports, resource/trust options unchanged. No local Lean, Lake, compiler or axiom audit. The original pre-extension packet, APP, intake, README and provenance bytes are retained under `HOSTED-43586414080/PRE-PREVENTIVE-EXTENSION`. Existing observed source reviews remain unchanged and do not approve the extended contract; fresh nine-obligation propagation review is required.

Hosted simplification/kernel checking remains pending for the observed Pasting repair and the three PREVENTIVE_UNOBSERVED connected consumers. The latter are source-predicted normalization risks, not observed failures or claimed passes. Full finite/infinity restriction maps and unchanged later Cech consumers still require hosted checking; source review and admission are not mathematical acceptance.
