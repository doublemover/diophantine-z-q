# Independent global geometry comparison source review: run 43568616769

## Verdict and observed evidence
No source-level blocker found in the frozen candidate. This is not a Lean/kernel pass, whole-packet acceptance or a claim that every observed conversion/timeout is fixed. No local Lean/Lake or user computer was used. Later propagation/metadata review is separate.

The exact before bytes match the published e3d4f334 center-r61 source; the own RESULT binds the published intake 3291e2636bde22d0f14e67c9bbd679196fb69ff5a3c39c449cd039ce15c5afee. That run records RationalInfinityMap passing in 8.378 seconds, followed by GlobalComparison failing in 38.577 seconds. Its log contains missing source-overlap Algebra at overlapIso and the infinity square, a finite-square mismatch, a 900000-heartbeat conversion timeout, and two residual chartEmbedding = cover.f Boolean-branch equations. The finite-square mismatch and timeout may be secondary, but source review alone cannot certify that diagnosis.

## Exact original actions, no new caller assumption
The two local Algebra instances are exactly IntegralFullOverlapLocalization.sourceAlgebra Q c and IntegralRationalFullOverlap.originalAlgebra c. Inspection of their exposed bodies identifies the first as the actual sourceMap.toRingHom.toAlgebra, and the second as the original orderToOpen composed with sourceEquiv, converted to an algebra. They are the same actions already used to define overlapEquiv by the universal property of the same full quartic localization, and explicitly installed in the hosted-passing FiniteAtlas producer. No arbitrary scalar action, extra compatibility premise or alternative overlap is introduced.

The public chart/isomorphism/theorem declarations and proof maps are unchanged. The exact finite, infinity and common rings, original signed ring equivalences, contravariant Spec-map orientations and all four twist-unit inputs are retained. In particular the infinity comparison still uses the full original restriction theorem covering the coordinate and all three signed ratio roots, rather than only root squares or a fraction-field surrogate.

## Full cover and inverse identity
The from_to proof now spells the right-hand side as the same original finite or infinity chartEmbedding followed by identity, instead of leaving an underscore that retains the cover projection. ContactGlobalSmooth.cover, chart and embedding are exposed definitions; their false/true branches are exactly those two embeddings. Thus this is the original cover hom-extensionality goal on both complete charts, not a smaller open or an assumed identity. The same toOriginal pushout.desc, fromOriginal glueMorphisms, actual full pullback intersection and original inverse equations remain in place.

The resulting originalModelIso is still the actual integral glued model over Q identified with the original global normalization, with exactly the existing signed finite/infinity chart maps. over_Q retains the original rational structure-map equation. No field/domain/nonempty hypothesis, omitted branch, coefficient rescaling or exceptional locus is added.

## Direct downstream contract
IntegralRationalFiveChartGeometry318 is the direct consumer: branch_toOriginal uses finite_toOriginal for every Fin4 branch, branch_open/infinity_open use the same originalModelIso, and branch_structure/infinity_structure consume over_Q for the original rational structure maps. That source is unchanged, with digest 0ef4ee4181840dc84c64110cce4d825eca1325c6b02491e3dbe5abaf190fda35. The copied branch/infinity coefficient modules independently use the original ring equivalences; they should not be mislabeled as direct consumers of GlobalComparison. The exact original embedding/isomorphism, not an abstract object with the same dimension, is what the downstream construction requires and still receives.

## Scope and remaining verification
The only edits are the two original-action registrations and the two explicit RHS identity composites. No resource/transparency/trust option is changed. The restored local instances do not become extra caller parameters: their values are defined by existing maps. The displayed type-conversion and kernel behavior must still be tested on hosted Lean; source plausibility does not establish success or later consumer elaboration.

Before SHA256: 708ffebf687e9723c612da342bd196cde48eeaa937a2487b6b4d554b30326b10
Candidate SHA256: ae7c435b0fe63478293a2ada58a3edc16e7c5b0406bb5f8da4dfa5344964e5dc
Own failure log: bdf24f829f3dab6b919afb13104da3e309988e3d7a0a9283a92e950de255604c
Own RESULT: 0ddace88fa8d7394a512c6d42f09e59937f06b016547eda934a309883068c7ee

The companion manifest pins exact primary/source/consumer evidence. Bind as source review only.
