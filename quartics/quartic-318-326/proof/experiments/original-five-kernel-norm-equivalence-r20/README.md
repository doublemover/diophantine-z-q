# original-five-kernel-norm-equivalence-r20

Draft successor to `original-five-kernel-norm-equivalence-r19` at `2af419e128047c483b3cdc0ba5e4d65c09d7c4ce`.

## Exact hosted evidence

Run 43597228569, job 132454817782, artifact 14115187935. OriginalDualAlgebraNormTrace318 remains the first failure in 14.537s. At norm_inl line47 the direct native norm-equivalence call tries to synthesize Module R Nat for the unannotated right tensor factor1; its equivalence argument then has a mismatched inferred carrier. The preceding OriginalRightTensorNormTrace318 remains passed. Existing actualAlgebra class-reducibility warnings are retained.

## Bounded repair

Annotate only the right tensor factor1 in the explicit norm_eq_of_algEquiv application as DualNumber R. This fixes the intended argument type already written in the calc endpoint and original equivalence domain. The original norm, actual right-base algebra equivalence, maps, finite/free hypotheses, all result statements and every other proof term remain unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

The annotation is a source-supported elaboration candidate, not a hosted pass. The exact native norm application and later whole-unit consumers still require hosted checking; the absence of a later diagnostic is not module acceptance. No new scalar action, limit or mathematical assumption is introduced.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
