# relative-original-normalized-kernel-gluing-r8

Draft successor to `relative-original-normalized-kernel-gluing-r7` at `b3d76fb41c03f9194b0613eac0a9b4cb04b2576c`.

## Exact hosted evidence

Run 43564923898, job 132357123329, artifact 14101789296. ContactRelativeWholeOpenSections318 passed in 16.652 seconds. RelativeCoefficientFunctor318 failed in 2.369 seconds in the two pure-tensor identity/composition goals: ringMap_tmul is unused against the explicit CommRingCat.Hom.hom applications.

## Bounded repair

In the two pure-tensor branches, simplify the already exposed original ringMap definition rather than the ringMap_tmul rewrite pattern. This reduces the same Algebra.TensorProduct.map with f on the coefficient factor and identity on the original chart factor. Additive induction and all public statements are unchanged.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

The two simplification repairs and later functoriality consumers require hosted Lean. No source pass or whole-packet success is asserted for this successor.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
