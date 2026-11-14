# relative-original-normalized-kernel-gluing-r14

Draft successor to `relative-original-normalized-kernel-gluing-r13` at `f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb`.

## Exact hosted evidence

Run 43586414080, job 132422325735, artifact 14110354609. ContactCoefficientSectionEquivalences318 passed in 2.418s. OriginalPullbackSquarePasting318 failed in 4.721s with three residuals: Iso.refl.hom at congr_first, pullback.map(identity) in H5, and reflexive/component-inverse projections in the final pasting comparison.

## Bounded repair

Normalize only those observed residuals: add native Iso.refl_hom in congr_first and the final simp list, qualify CategoryTheory.Functor.map_id in H5, and use native Iso.app_inv in the final simp list. All comparison definitions, path proofs, public statements, A1–A8 objects and H1–H5 equations retain the same maps and orientation.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted simplification/kernel checking of these categorical equalities remains pending. Later full coefficient restriction-square consumers are unchanged and not claimed compiled. Native source review and metadata admission are not whole-packet or mathematical acceptance.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
