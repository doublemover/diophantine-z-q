# original-five-kernel-norm-equivalence-r18

Draft successor to `original-five-kernel-norm-equivalence-r17` at `f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb`.

## Exact hosted evidence

Run 43586414080, job 132422325691, artifact 14110328931. OriginalTensorTraceBaseChange318 passed in1.868s and OriginalRightTensorNormTrace318 in2.018s. OriginalDualAlgebraNormTrace318 failed in3.271s: norm_inl cannot definitionally replace inl x by the actual tensor equivalence image, and norm_unit cannot infer the intended algebra equivalence for the unspecialized norm rewrite.

## Bounded repair

In norm_inl replace the failed definitional change with the original DualNumberScalarExtension.equivalence_left equality, then instantiate Algebra.norm_eq_of_algEquiv with the exact original equivalence and tensor argument. Instantiate the same native theorem with that equivalence and z.val in norm_unit. All public statements, actualAlgebra/equivalence definitions, finite-free transport, unit hz/hn witnesses and downstream maps remain unchanged.

## Scope and verification

213 root modules in the original order; 1 changed and 212 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted typeclass/coercion matching, rewrite and kernel checking remain pending. The same original algebra equivalence is supplied explicitly rather than guessed; no subsequent dual-unit identification or affine-section norm consumer is claimed compiled. Existing class-reducibility warnings are retained.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
