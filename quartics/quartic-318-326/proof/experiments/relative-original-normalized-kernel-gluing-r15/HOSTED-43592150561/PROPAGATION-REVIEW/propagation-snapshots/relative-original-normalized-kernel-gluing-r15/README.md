# relative-original-normalized-kernel-gluing-r15

Draft successor to `relative-original-normalized-kernel-gluing-r14` at `75be14ed25ed39f46289f1c69914810afd46068c`.

## Exact hosted evidence

Run 43592150561, job 132439484873, artifact 14113485810. OriginalPullbackSquarePasting318 passed in 8.029s and OriginalSectionPullbackComposition318 passed in 4.022s. OriginalLineSquareSections318 failed in 5.374s: hs retains an identity before the inverse comparison, and both bare naturality rewrites fail pattern matching on the original section maps.

## Bounded repair

Add native Category.id_comp to the existing hs simp-only normalization. Replace the two bare naturality rewrites by direct fully specialized OriginalSectionPullbackComposition.naturality equalities under congrArg of the unchanged outer comparison/path maps: inverse orientation for the first calc step, forward orientation after the unchanged hs rewrite for the last. Original theorem, full section domain, all maps/path proofs, hp/hs claims and coefficient actions are unchanged.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

This is a source-reviewed candidate, not yet a hosted pass. The direct equalities still require concrete elaboration/kernel checking. Later finite/infinity restriction squares retain the prior preventive normalization edits without a newly observed result; no further source edit or success is inferred for those consumers.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
