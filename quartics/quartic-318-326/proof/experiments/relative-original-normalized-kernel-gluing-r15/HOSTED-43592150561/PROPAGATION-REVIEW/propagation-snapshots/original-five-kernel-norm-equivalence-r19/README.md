# original-five-kernel-norm-equivalence-r19

Draft successor to `original-five-kernel-norm-equivalence-r18` at `75be14ed25ed39f46289f1c69914810afd46068c`.

## Exact hosted evidence

Run 43592150561, job 132439484844, artifact 14113377247. OriginalDualAlgebraNormTrace318 still failed in 3.070s. Its only hard diagnostic is norm_inl line42: the explicit norm-equivalence rewrite does not match the current norm of the exact equivalence image. The norm_unit proof has no hard diagnostic in this run; existing actualAlgebra class-reducibility warnings remain.

## Bounded repair

Replace only norm_inl’s chained rewrite with an explicit calculation: map the original equivalence_left equality through the actual dual-base norm, apply the native norm_eq_of_algEquiv directly with explicit base DualNumber R and the same equivalence/pure tensor, then use the unchanged original norm_coefficient and algebraMap_eq_inl formulas. The actual algebra, equivalence, finite_free, norm_unit and public norm_inl statement are unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Exact equality-term elaboration, native coefficient matching and kernel checking remain hosted-pending. No claim is made that the earlier norm_unit lack of diagnostic is a whole-module pass or that subsequent all-unit norm consumers compile. Original class reducibility warnings are preserved.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
