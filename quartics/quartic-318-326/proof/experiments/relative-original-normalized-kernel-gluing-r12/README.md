# relative-original-normalized-kernel-gluing-r12

Draft successor to `relative-original-normalized-kernel-gluing-r11` at `977040de03da47698b89a3345d93e2ffcbc2220c`.

## Exact hosted evidence

Run 43578868567, job 132399604852, artifact 14107004005. OriginalCoefficientTensor318 passed in 7.631 seconds. OriginalCoefficientSections318 failed in 3.072 seconds: the local Algebra R S instance hides f and is rejected, followed by missing Module R S in coefficient tensor expressions and a resulting unsolved goal.

## Bounded repair

Remove the invalid hidden-f local instance registration. Scope equivalence, unit and pure_tensor types and bodies with the existing exposed OriginalCoefficientTensor.coefficientAlgebra k R S f, whose entire body is the original f.toAlgebra. The mathematical equivalence composition and both original proofs are unchanged. Public type text intentionally gains letI scopes; no caller premise, scalar action, native map, source/target section object or tensor domain is replaced.

## Scope and verification

1298 root modules in the original order; 1 changed and 1297 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted checking of these scoped original section equivalences remains pending. Later ContactCoefficientSectionEquivalences and ContactCoefficientNativeSections retain their own hidden-f local instances and are not modified or claimed verified. Source review/Python admission are not candidate Lean, whole-packet or theorem acceptance.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
