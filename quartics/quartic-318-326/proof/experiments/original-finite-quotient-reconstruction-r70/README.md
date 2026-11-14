# original-finite-quotient-reconstruction-r70

Draft successor to `original-finite-quotient-reconstruction-r69` at `f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb`.

## Exact hosted evidence

Run43586414080, job132422325730, artifact14110598895. OriginalFiberPointReconstruction318 passed in 2.120s. OriginalFiniteProjectiveFlat318 failed in 3.373s: the unexposed JLineAtlas.cover index does not reduce to Fin 2 at chart application. The preceding affine_flat body has warnings but no reported hard error in this log.

## Observed repair and connected preventive scope

Observed-frontier repair: Replace only the use of the unexposed imported cover with a literal local OpenCover having the same Fin 2 index, both entire polynomial affine charts, the exact JLineAtlas.chart maps and the standard_opens_cover proof. The block is identical to the one in the already hosted-passing OriginalProjectiveBaseIntegral.reduced. Original affine_flat and all remaining flatness arguments and public statements are unchanged. Separately source-reviewed PREVENTIVE_UNOBSERVED connected repair: remove the two invalid hidden-p local registrations in OriginalFinitePointReconstruction and install the exact derived baseIntegral p and actualBase p scopes in original_curve result type and proof. Its public result-type text changes and the two local names are removed; no new caller premise or conclusion is introduced. The originalFlat instance, exact FiberPoint call and full curve/field/map conclusions remain.

Preventive modules: `OriginalFinitePointReconstruction318`. Each remains **PREVENTIVE_UNOBSERVED**, separately source-reviewed and never asserted to have failed in the hosted log.

## Verification

80 root modules in the original order; 2 changed and 78 byte-identical. No modules added/deleted; imports, resource/trust options unchanged. No local Lean, Lake, compiler or axiom audit. The original pre-extension packet, APP, intake, README and provenance bytes are retained under `HOSTED-43586414080/PRE-PREVENTIVE-EXTENSION`. Existing observed source reviews remain unchanged and do not approve the extended contract; fresh nine-obligation propagation review is required.

The flatness candidate and final original_curve consumer both require hosted elaboration/kernel checking. Only flatness is an observed current failure; the final consumer edit is PREVENTIVE_UNOBSERVED. Derived result-type scopes are not byte-identical public statement text. No baseline module is changed or reclassified, and no whole-packet or mathematical acceptance is claimed.
