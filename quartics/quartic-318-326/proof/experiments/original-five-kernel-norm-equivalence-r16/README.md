# original-five-kernel-norm-equivalence-r16

Draft successor to `original-five-kernel-norm-equivalence-r15` at `977040de03da47698b89a3345d93e2ffcbc2220c`.

## Exact hosted evidence

Run 43578868567, job 132399604839, artifact 14108040790. OriginalTwoOpenGaugeLog318 passed in 2.522 seconds; hosted compilation then passed OriginalHOnePointedEquivalence318, OriginalHOneKernelGroupEquivalence318, OriginalFivePointedClassification318 and SquareZeroNormTrace318. OriginalTensorTraceBaseChange318 failed in 1.668 seconds: after generic ext z, z has type S rather than a tensor, so TensorProduct.induction_on rejects the target. The induction_on deprecation is a separate warning.

## Bounded repair

Replace generic ext z by explicit apply LinearMap.ext followed by intro z. This fixes the induction domain to the entire original A tensor S without recursively invoking tensor extensionality first. Every original zero, pure-tensor and addition induction case is unchanged, as are all multiplication, trace, norm and infinitesimal-norm statements and proof expressions after that introduction.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

The preserved tensor induction and downstream trace/norm comparisons still require hosted elaboration/kernel checking. The existing induction_on deprecation warning is intentionally retained rather than bundled with this narrow error repair. No module, whole packet, subsequent right-oriented consumer or theorem acceptance is claimed.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
