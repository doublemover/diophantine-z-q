# original-finite-quotient-reconstruction-r64

Draft successor to `original-finite-quotient-reconstruction-r63` at `b3d76fb41c03f9194b0613eac0a9b4cb04b2576c`.

## Exact hosted evidence

Run 43564923898, job 132357123308, artifact 14102365547. OriginalIntegralBaseReconstruction318 passed in 2.622 seconds and OriginalNormalCoverSections318 in 2.270 seconds. OriginalCanonicalAffineChart318 failed in 2.371 seconds: line 59 applies the implicit-parameter pullback.condition as a function; line 70 lacks Nonempty for the entire top-open subtype.

## Bounded repair

Name the implicit f/g parameters of the same categorical pullback condition. Construct the required Nonempty top-open subtype from the existing chart_nonempty p before applying sections_of_stalks. No theorem statement, chart, coefficient map, normal-cover hypothesis or domain changes.

## Scope and verification

80 root modules in the original order; 1 changed and 79 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

The new module and all later consumers still need hosted Lean checking. The next CanonicalAffineReconstruction has unverified hidden-parameter local instances, left unchanged. No kernel budget or trust option changes.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
