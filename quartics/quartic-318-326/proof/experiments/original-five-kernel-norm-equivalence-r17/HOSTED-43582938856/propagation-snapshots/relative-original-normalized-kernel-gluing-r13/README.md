# relative-original-normalized-kernel-gluing-r13

Draft successor to `relative-original-normalized-kernel-gluing-r12` at `6fe85071934d36d22cfdbd7c503f6b9a54e6ef18`.

## Exact hosted evidence

Run 43582938856, job 132411887337, artifact 14109432878. OriginalCoefficientSections318 passed in 3.273 seconds. ContactCoefficientSectionEquivalences318 failed in 6.030 seconds: hidden-f local Algebra R S registration is invalid, then overlap_unit cannot synthesize Module R S.

## Bounded repair

Remove the invalid local coefficient-algebra registration and explicitly scope overlap_unit type and body with the same native coefficientAlgebra (CommRingCat.of ℚ) R S f, exactly f.toAlgebra. All three finite/infinity/overlap equivalence abbreviations and the original unit application are unchanged. Public type text intentionally gains a derived letI scope, without a new premise or changed action.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted checking of the scoped overlap unit remains pending. Later coefficient-native consumers retain their own hidden-f registrations and are not claimed compiled. Source review/Python checks are not whole-packet or mathematical acceptance.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.

## Consumer-search scope

No direct qualified use of this namespace overlap_unit was found in the current 1298-root packet. The identified actual NativeSections consumers use the three equivalence abbreviations; no direct overlap_unit consumer is asserted.
