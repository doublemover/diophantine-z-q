# Actual normalized chart inputs for finite cotangent images

Status: inactive source-only draft, independently review-pending, not locally or remotely Lean-checked. This bundle constructs prerequisites on the actual existing normalized finite/reciprocal orders; it does not construct a regular/maximal model, its dualizing lattice or a global Kodaira–Spencer map.

## What is newly derived

`NormalizedChartFiniteType318.finite_order` and `infinity_order` use the existing concrete `finite_free` theorems for the full four-root orders over V[X], native module-finite-to-algebra-finite-type, polynomial finite type and finite-type transitivity. The same V-algebra and whole order are retained. No localization, denominator inversion, unit-twist hypothesis, smoothness or extra finite-type premise is used.

`pointAlgHom` upgrades the already constructed ring hom to a V-algebra hom by the existing `NormalizedValuativeChartStructure318.scalar_identity`, whose proof evaluates the actual polynomial map on each constant. The underlying ring hom is definitionally unchanged, explicitly recorded by `pointAlgHom_toRingHom`. The same-universe binder matches this existing scalar theorem and the concrete order; it is not a new mathematical hypothesis.

`NormalizedIntegralPointInput318.chart_center_alg` applies the original all-place `chart_center` once. It retains exactly its normalized units u, parity exponents e, nonzero field rescalings s, common twist identities, finite or reciprocal coordinate, and all four signed original roots. Only the existing ring points are bundled with their proved base-linearity. Thus this is an existential integral algebra point on one of the actual named charts, not an assumed new point or an arbitrarily chosen algebra action.

`pointAlgebra` is exactly the algebra structure induced by that point's underlying ring hom. `point_tower` supplies its compatibility with V→A. `cotangent_finite` derives finiteness of the genuine V ⊗[A] Ω(A/V) and its tensor square from native Kaehler finiteness and module base change. The finite/reciprocal specializations discharge the finite-type premise using the preceding concrete results. This pullback is not Ω(K/V) and is not silently identified with a dualizing fiber.

## Connection to the finite-image construction

The frozen, independently review-pending `geometry-module-image-frames` consumer uses a finite-type chart A, a compatible integral point A→V, a V-linear functional on this cotangent pullback and lifts of the two original sections. Here the actual normalized orders supply the first two inputs and finiteness. The consumer's `quadraticEvaluation` and range/free-frame constructions remain unchanged. This bundle does not yet provide the functional or section lifts and therefore does not claim that the resulting image is the original maximal-model bicanonical lattice.

The exact consumer sources and APP snapshot are retained only as pending-review primary context, not as accepted imports or evidence of a completed composition. The proposed inactive closure is the published center-r68 96-source closure plus these two sources. No active packet/index or producer dependency is changed.

## Good and bad charts, remaining inputs

The original chart-center statement applies at every DVR with the displayed original point data, including nonunit twists, nonintegral t and residue characteristic two. Its finite case includes t=0; its reciprocal case explicitly retains t≠0, w=t⁻¹ and nonunit w. All four roots, not merely a dense-open subset, are retained.

“Normalized” here refers to the original twist normalization and existing named orders; it does not assert that these rings are integrally closed. These potentially singular charts are not assumed regular, smooth or maximal. The existing good-chart cotangent-frame argument cannot be transferred to all bad charts without proving its hypotheses. Finiteness of cotangents alone gives neither torsion-freeness/rank one nor a dualizing/canonical comparison.

Still required: the actual generic cotangent evaluation functional in the original field; its compatibility with the chosen chart and the two original quadratic section lifts; an identified appropriate regular/maximal integral model and its dualizing/bicanonical lattice; the actual native Hodge determinant and KS map with its lower-image inclusion and metric pullback. No degree, metric, finite support, defect bound or per-point GeometricRealization is concluded by this bundle. Earlier conditional native-q sign results remain separate.

## Provenance and verification

Project primaries are pinned to published 57227e167abe49436d651b932ff75d5bdf9b5898. Native Mathlib APIs are pinned to 56a005855ea17e0b0958f73ec801ae140b0a1679. All 96 inherited source hashes are checked against that Git commit. The nine application obligations bind this whole document, exact construction and current pending consumer. Static no-admission/import/order/provenance checks and the repository audit self-test are not Lean elaboration or mathematical acceptance. Historical global applicability is unresolved, not newly disproved.
