# original-five-kernel-norm-equivalence-r17

Draft successor to `original-five-kernel-norm-equivalence-r16` at `6fe85071934d36d22cfdbd7c503f6b9a54e6ef18`.

## Exact hosted evidence

Run 43582938856, job 132411887302, artifact 14109303935. OriginalTensorTraceBaseChange318 failed in 1.719 seconds. Explicit LinearMap.ext now reaches the whole tensor induction. The sole hard error is its pure-tensor case, whose goal retains LinearMap.mul applications on both sides. Deprecation/unused-simp/unnecessary-simpa messages are warnings, not extra hard errors.

## Bounded repair

Add only the pinned native LinearMap.mul_apply' identity to the existing simp-only list in the tensor pure case. It definitionally evaluates the same linear multiplication maps so the original tensor multiplication and one_mul rules apply. Every statement, action, extensionality step, induction branch, trace/norm/infinitesimal formula and downstream map remains unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted simplification/kernel checking remains pending, including later trace/norm and right-oriented consumers. Existing induction_on deprecation is retained. Source/metadata review is not Lean success, packet acceptance or a proof of the arithmetic theorem.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
