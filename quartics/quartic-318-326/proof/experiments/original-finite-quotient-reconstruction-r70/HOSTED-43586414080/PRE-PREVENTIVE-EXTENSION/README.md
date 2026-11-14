# original-finite-quotient-reconstruction-r70

Draft successor to `original-finite-quotient-reconstruction-r69` at `f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb`.

## Exact hosted evidence

Run 43586414080, job 132422325730, artifact 14110598895. OriginalFiberPointReconstruction318 passed in 2.120s. OriginalFiniteProjectiveFlat318 failed in 3.373s: the unexposed JLineAtlas.cover index does not reduce to Fin 2 at chart application. The preceding affine_flat body has warnings but no reported hard error in this log.

## Bounded repair

Replace only the use of the unexposed imported cover with a literal local OpenCover having the same Fin 2 index, both entire polynomial affine charts, the exact JLineAtlas.chart maps and the standard_opens_cover proof. The block is identical to the one in the already hosted-passing OriginalProjectiveBaseIntegral.reduced. Original affine_flat and all remaining flatness arguments and public statements are unchanged.

## Scope and verification

80 root modules in the original order; 1 changed and 79 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

The full flatness theorem still requires hosted elaboration/kernel checking. The actual OriginalFinitePointReconstruction consumer retains its own hidden-p local instance registrations and remains unmodified/unverified. No baseline module is changed or reclassified.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
