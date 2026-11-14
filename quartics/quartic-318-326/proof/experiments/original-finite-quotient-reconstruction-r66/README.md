# original-finite-quotient-reconstruction-r66

Draft successor to `original-finite-quotient-reconstruction-r65` at `52ab6e7faba5ec87dd4a1aa9d6cadcaef66aebca`.

## Exact hosted evidence

Run 43572239136, job 132379354880, artifact 14104414569. OriginalCanonicalAffineReconstruction318 passed in 2.370 seconds. OriginalSchemeBranchReconstruction318 failed in 2.871 seconds: eval₂_X.symm was parsed as an unknown constant, an uninstantiated polynomial_map rewrite had a metavariable pattern, and hidden-p baseIntegral registration failed, followed by integral-base elaboration errors.

## Bounded repair

Use simp only on the original polynomial-generator identity, instantiate polynomial_map at the exact r.comp of the original chart coefficient, and scope the original integral-base proof and native quotient field algebra/finite-dimensional/Galois structures explicitly. The final structures are obtained from the same field_structure theorem and existing inputs, not additional caller assumptions. Public type scopes intentionally change; the original branch law and reconstruction objects do not.

## Scope and verification

80 root modules in the original order; 1 changed and 79 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted elaboration of this candidate remains pending. The direct later fiber-point consumer still has independent hidden-parameter local instances and is not claimed checked. Public letI type text changes are disclosed, rather than claiming identical signatures.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
