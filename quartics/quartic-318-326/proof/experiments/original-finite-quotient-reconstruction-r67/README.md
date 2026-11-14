# original-finite-quotient-reconstruction-r67

Draft successor to `original-finite-quotient-reconstruction-r66` at `d97d209a1666cdcb0d7ae2488523fbfa7d46fae6`.

## Exact hosted evidence

Run 43575728180, job 132389976200, artifact 14105564844. OriginalSchemeBranchReconstruction318 passed in 2.119 seconds. OriginalFiniteDeckDegree318 failed in 1.267 seconds: explicit FaithfulSMul lambda binders did not match implicit fields, AlgEquiv.map_smul was unavailable, local intermediate-field finrank did not match native subfield finrank, and fixedness could not unfold the unexposed imported action.

## Bounded repair

Use the literal MulSemiringAction.compHom L ρ that is the complete body of the original action, annotate the faithful-action lambda binders as implicit, and use the same automorphisms native linear map for scalar commutation. Explicitly normalize the fixed intermediate field to its native fixed subfield for the finrank theorem and normalize membership to the original ρ-fixed equation. The public theorem and its original tower argument are unchanged; no Galois or fixed-field premise is added.

## Scope and verification

80 root modules in the original order; 1 changed and 79 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted checking of the explicit native fixed-field carrier conversion remains pending. The later original quotient-rank consumer retains separate hidden-p instances and is not claimed verified. Source review and Python admission are not Lean or whole-packet acceptance.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
