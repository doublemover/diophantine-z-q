# original-five-kernel-norm-equivalence-r14

Draft successor to `original-five-kernel-norm-equivalence-r13` at `52ab6e7faba5ec87dd4a1aa9d6cadcaef66aebca`.

## Exact hosted evidence

Run 43572239136, job 132379354878, artifact 14105223173. OriginalOpenExponentialNaturality318 passed in 1.870 seconds. OriginalTwoOpenGaugeLog318 failed in 2.271 seconds: reduced_appLE inferred the Bool-indexed opens instead of the explicit affine U/V instances; rewriting the gauge exposed incompatible bundled/native unit multiplication; the projected exp_restrict rewrite then failed. letI messages were warnings, not failures.

## Bounded repair

Supply the original U and V explicitly to reduced_appLE. Add a private generic whole-open gauge bridge that checks the actual structure-unit presheaf equation on native section-unit carriers before specializing to the original thickening. Instantiate it with the unchanged original_forward/exp_original identities; compose the exact instantiated exp_restrict equalities under congruence rather than rewriting projected dependent carriers. The public logarithm statement, full original opens, gauge, finite-minus-infinity sign and of_iso consumer remain unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

This candidate is source-only until hosted checking. The generic native-carrier bridge and concrete specialization still require Lean elaboration/kernel verification. No injectivity of original H1, global theorem acceptance, full packet pass or future consumer success is inferred.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
