# relative-original-normalized-kernel-gluing-r10

Draft successor to `relative-original-normalized-kernel-gluing-r9` at `52ab6e7faba5ec87dd4a1aa9d6cadcaef66aebca`.

## Exact hosted evidence

Run 43572239136, job 132379354908, artifact 14105360792. OriginalCoefficientTensor318 failed in 4.374 seconds. Its original hidden-f algebra errors are gone; three proof branches remain: native ringMap hom projection in ringEquivalence_right, projected linear-equivalence map_smul rewriting, and the final distributivity equation in tensorTransport addition. Class-definition/letI style messages are warnings, not failures.

## Bounded repair

Repair only those three proof branches: unfold the exact native ringMap and coefficientAlgebra in the tensor-generator calculation, apply the exact linear-equivalence map_smul equality beneath congrArg rather than rewrite its projected head, and give an explicit additive/distributive calculation. Public declarations, full tensor objects, exact coefficient/old-chart actions and all original maps are unchanged.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

No candidate Lean success is claimed. Later OriginalCoefficientSections still has an independent hidden-f algebra registration and remains unverified. The native whole-ring and tensor induction proofs retain every case; no basis or finite-free assumption is introduced.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
