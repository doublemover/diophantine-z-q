# relative-original-normalized-kernel-gluing-r11

Draft successor to `relative-original-normalized-kernel-gluing-r10` at `d97d209a1666cdcb0d7ae2488523fbfa7d46fae6`.

## Exact hosted evidence

Run 43575728180, job 132389976169, artifact 14106294132. OriginalCoefficientTensor318 failed in6.230 seconds. Two residual errors remain: algebraMap R S r tensor b versus f r tensor b after native tensor simplification, and the toLinearEquiv coercion in map_smul versus the actual algebra-equivalence application. The prior additive calculation has no reported failure; class/letI messages are warnings.

## Bounded repair

Only two proof normalization additions: close the residual coefficient-algebra definitional equality with rfl after the unchanged simplifier, and include the pinned native AlgEquiv.coe_toLinearEquiv theorem in the existing pure-tensor congruence simplification. All public statements, exact f-induced actions, entire tensor modules and original maps remain unchanged.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

These two explicit normalization steps still require hosted elaboration/kernel checking. The later coefficient-sections and tensor-section consumers have not been verified. No new assumption or statement change is used to avoid the residual equalities.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
