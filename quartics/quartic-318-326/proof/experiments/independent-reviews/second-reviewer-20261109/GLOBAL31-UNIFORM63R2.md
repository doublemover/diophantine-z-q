# Bounded review: actual integral global pair and numerical norm repair

Reviewer: /root/advance_height_realization. Implementers: /root/complete_analytic_geometry (height), /root/construct_integer_witnesses (arithmetic). Date: 2026-11-09.

This is internal independent source review of the five new global-pair modules and the one arithmetic successor repair. The reviewer authored older height predecessors; their independent review remains the main integrator's work. This report does not represent a new independent audit of those predecessors. No local Lean command, compilation, or build was run. Hosted elaboration and recursive axiom audit remain required.

## Integral global pair, 31-source closure

Packet: height-integral-global-pair-r1. Intake SHA256: 187aa8f231021f22367e5ceb8eaab99b598b65db1455d6246cbe822485dba1b1. All 26 sources from height-integral-glued-model-r2 are byte-identical. I read all five new sources, the nine application obligations and README, and the directly consumed square-coordinate derivative, weighted-square naturality/cancellation, product-localization, pushout-intersection, and module-sheaf gluing sources.

IntegralAllBranchOverlapMaps318 constructs the maps from every original branch ring into the same finite/infinity overlap. The quartic is a unit because the original coordinate t is the unit-scaled square of y0 and the original branch-zero denominator is inverted. The exact polynomial factorization then makes each other denominator a unit. Away.lift supplies the actual maps with source and polynomial restriction identities. The branch-zero map is identified with the existing finiteMap; the new maps are open immersions by their composition with the actual source localization.

IntegralBranchTensorTransport318 transports the original cleared coefficient identity and the universal derivative through those specified algebra maps. The derivative coefficient remains 2*c_i^-1*y_i. Cancellation takes place by a unit of the whole common ring, not by a nonzero generic value. Both section indices retain the original J squared and the second section's original t factor. The argument does not divide by J and does not require a domain.

IntegralAllBranchChartGeometry318 proves every branch route into the actual pushout and every full finite/infinity image intersection using GenericOpenPushout318.exists_overlap. Containment of the original overlap in every branch is established first; the reverse containment uses the whole finite chart and the pushout's actual point-equality witness. This does not silently replace a common open by the full intersection.

IntegralFinitePairGeometry318 instead uses the literal localization at D_i*D_j for finite pairs. The two lifts agree on SourceOrder. ReciprocalOverlapBase318.away_of_mul establishes the subsequent localization structures under these exact scalar maps, and basicOpen_mul plus the open embedding's image_inf supplies the full intersection, including equal indices. For distinct indices the two three-factor denominators together contain every one of the four original factors. The twelve ordered unequal cases are exhausted explicitly. Unit twists are retained before passing from twisted to untwisted denominators. The proof helper pair_units was made public before freeze to avoid a preventable strict-module visibility concern; no mathematical statement changed.

IntegralGlobalBicanonicalPair318 invokes weightedSquare_restrict_to on these actual finite-pair maps and on the original finite/infinity maps. Thus equality of mapped expressions is equality of actual intrinsic tensor-sheaf restrictions. The common finite/infinity expression is joined through branch zero to the already constructed signed reciprocal differential compatibility. Compatibility covers all Option(Fin4) pairs, with equal indices reflexive, reversed finite/infinity pairs symmetric, and both section indices covered. ModuleGlobalSections318.gluedTop requires exactly the whole-open cover and the displayed full-intersection compatibility, both supplied here. q_restrict recovers every literal local formula.

The global pair requires IsUnit(2276931686400000:R); the separate frame results retain IsUnit(2:R). This is an integral construction away from the stated exceptional places, not an all-place model. Properness, separatedness, identification of the rational fiber with the original complete normalization, bad-prime extension, and the final metric/height comparison remain open. No new whole-proof claim is accepted.

## Arithmetic numerical norm repair, 63-source closure

Packet: forward-uniform-pole-domain-r2. Intake SHA256: 1afe14c843d7039f2888cc832df8a66b4dc88c420807af8aa1813e648abca0d9. Exactly one source changes from reviewed r1: PadeRatioWitness318.lean. Removing the 26 new occurrences of ,QuadraticAlgebra.norm_def reconstructs the predecessor source exactly; all 62 other sources are byte-identical.

I read the exact aa7e902 hosted failure, the changed projection proofs and their unchanged Relations/rows/fill definitions, and Mathlib/Algebra/QuadraticAlgebra/Basic.lean at 56a005855ea17e0b0958f73ec801ae140b0a1679. The primary source defines norm(z)=re(z)^2+b*re(z)*im(z)-a*im(z)^2 and inverse(z)=norm(z)^-1 times star(z). For scalar numerals 5,13,65,195 the imaginary part vanishes and the norm is their square. The failed residuals retain precisely these unevaluated norms. Adding norm_def to the existing projection normalization therefore addresses the displayed obstruction without adding assumptions, altering any source row, changing the witness, or commuting quantifiers. This is a justified proof-only repair; hosted success is not inferred.

The earlier UNIFORM63 review remains applicable to unchanged mathematical content. Actual compact-orbit membership and simultaneous normalized PointPair production remain explicit open prerequisites.

## Checks and disposition

Static packet source/import/hash validation passes for 31 sources with 179 baseline dependencies and 63 sources with 127 baseline dependencies. Exact predecessor comparisons above pass. Audit-history self-test passes its historical and application negative controls; this is structural validation only. The nine global-pair obligations have been compared to the constructed objects, quantified indices, maps and final consumers. Bounded source review supports scheduling both frozen candidates for hosted checking. The accepted baseline and whole arithmetic theorem are unchanged.
