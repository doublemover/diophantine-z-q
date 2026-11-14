# original-five-kernel-norm-equivalence-r13

Draft successor to `original-five-kernel-norm-equivalence-r12` at `e3d4f3341daf299c5658e7e9fe2f276f2e6aa58e`.

## Exact hosted evidence

Run 43568616769, job 132368407545, artifact 14103568940. SplitReducedGauge318 passed in 3.473 seconds. OriginalOpenExponentialNaturality318 failed in 2.571 seconds only at the unit_restrict rewrite in exp_restrict: the generic restriction pattern did not match the displayed original presheaf ring-hom projection. The unused affine-instance warning on reduced_appLE is not a failure and is left unchanged.

## Bounded repair

After the unchanged two exp_original rewrites, explicitly instantiate the existing unit_restrict theorem with the same thickening, epsilon, epsilon_square, full inverse-image restriction inequality and actual coefficient section. Compose that exact equality with the unchanged naturality proof rather than asking rewrite to discover its projected ring-hom carrier. All public statements and inputs remain unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted checking of this explicit theorem application and later consumers remains pending. No source-level review or structural check is a kernel or whole-packet pass.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
