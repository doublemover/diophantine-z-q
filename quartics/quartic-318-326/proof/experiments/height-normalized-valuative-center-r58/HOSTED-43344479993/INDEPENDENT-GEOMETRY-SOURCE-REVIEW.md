# Independent bounded geometry source review

Reviewer: arithmetic_repair_resume, distinct from geometry_repair_resume.
Review date: 2026-11-13. Comparison baseline: 4d85d68746c3729658dd5f85869f7dd4fc2b505f, exact hosted run 43344479993.

Disposition: no source-level blocker found in these bounded elaboration repairs. Accepted for the next hosted experiment, not as Lean/kernel success, global source acceptance, manuscript integration, or completion of the arithmetic theorem. No Lean or Lake command was run.

## IntegralRationalInfinityMap318

Read the complete before/after module, exact hosted failure log, IntegralInfinityOriginalField318, IntegralInfinityChart318, IntegralOverlapChartMaps318, IntegralOverlapRootGenerators318, IntegralRationalInfinityCoordinate318, and the baseline ThreeRootCoordinates318.ringHom_ext.

The typed mapped_smul helper expands precisely the given CommonBase action on the same overlap tensor algebra and maps the resulting product. It does not install an alternative scalar action. The old inverse root, its sign, all three ordered roots, and final y_j/y0 formulas are retained.

The rational_polynomial_ext helper covers every rational constant. The pinned Mathlib Rat/Cast/Defs source supplies RingHom.ext_rat for arbitrary ring homomorphisms into a semiring, so no unproved compatibility with a chosen rational algebra is assumed. Polynomial extensionality adds the X equation. Localization extensionality extends this to the entire original principal-localized polynomial base. ThreeRootCoordinates318.ringHom_ext then covers that complete base plus every j : Fin 3. Presentation at the coefficient vector is the original infinity order: its denominator is exactly the product of the same three coefficient polynomials.

The final field_restriction still compares the same two full ring homomorphisms. The reciprocal coordinate and rationalOrderEquiv_generator equalities supply their exact coordinate/root equations, and the original open-field injectivity remains the consumer in infinity_restriction. No scalar, case, denominator, transition map, or quantifier is discarded.

## IntegralOriginalInfinityEmbedding318

Read the complete before/after module, exact dependent-rewrite/instance failure, and pinned Mathlib OpenImmersion source. The failing opensRange rewrite had an IsOpenImmersion proof depending on the morphism being rewritten. Projecting to the underlying set before rewriting removes that proof from the rewrite motive. The subsequent opensRange_comp_of_isIso equation is mapped to underlying sets and composed with the same localization_away_comap_range equality. This still identifies the image of the original tensor right inclusion followed by its ring equivalence with the same denominator basic open.

The local instance supplied in inclusion_range is exactly localization_equiv_open at the unchanged concrete P,F,A,B,x,e. It does not assume new openness or change the public inclusion. All generic commutative-ring and localization hypotheses remain the same; no field/nonzero-denominator hypothesis is introduced.

## Verification boundary

I independently compared ordered module lists, every unchanged module's bytes, imports, option/attribute lines, the exact changed proof bodies, and unchanged public theorem declarations. The two packets have 96 and 173 modules respectively, changing one and two modules. Their identical rational-infinity-map copies have identical hashes. New private helpers are proved in source, but successful elaboration, absence of further recursion/typeclass blockers, and recursive axiom audit require hosted execution. Existing limits are not increased.

## Exact reviewed bindings

### height-normalized-valuative-center-r56
- `intake.json`: `aaeacfce493a68ccc3a436a5cf8483a525755519ea46036d3e22802ee14bc1e9`
- `APPLICATION.json`: `fc7d3a458b5a590570be8dac313832de27b634af3970af2ce2403068d6be8b7a`
- `README.md`: `30a312c4fa5aa0404e59050133c83bf7666eeffba41db8fbb57329a8b5ccf2d2`
- `IntegralRationalInfinityMap318.lean`: `b3a37fb56e341a83585bf2a8c887c2b006aecde39b5d9e8ed1307dd99469064d`

### height-original-ks-lattice-assembly-r7
- `intake.json`: `47297de0bd1a0ad58b580106b0f6bb3b8a7d42bcffdc551d3c8f3ae413ea7c1f`
- `APPLICATION.json`: `814c62b009103fec3323781e2943f026c91b12b6e2a115007fb39bdf4f9aed24`
- `README.md`: `cad0a3ee57091582ad7e4b582c032ee7306c3198cdf6ca7ac86ab9b882468946`
- `IntegralRationalInfinityMap318.lean`: `b3a37fb56e341a83585bf2a8c887c2b006aecde39b5d9e8ed1307dd99469064d`
- `IntegralOriginalInfinityEmbedding318.lean`: `a3286e4829e0a388ef00169d4bdfb1d571effc6f89950b919a3b0961fec35970`

## Metadata refresh acknowledgment

The author subsequently added SOURCE_VALIDATION.json and its APPLICATION.bindings entry. I read that source-only validation record and checked the binding hash. Lean sources, intake and README are unchanged. The application hashes above are the refreshed reviewed hashes; the report accepts no additional mathematical claim.

## Exact-copy propagation to normal infinity trace

I compared height-original-normal-infinity-trace-r3 and r4 before propagation. Their IntegralRationalInfinityMap318 hash is 18b1e9df062406c92a965e0d9088151904701e59ebfa68c3493b4728d860f5b2 and IntegralOriginalInfinityEmbedding318 hash is 36cfeaa066bdbe52a7de9c85139cf5171aef287bf2ee4e4876973a33189a752c. Both are exactly the reviewed geometry before sources. The normal-trace 1504-module order is unchanged. Copying the exact reviewed after hashes listed above into r4 preserves the same public maps, carriers and theorem interfaces, so this bounded propagation has no source-level blocker.

Recursive dependency comparison found one byte difference from the geometry packets: IntegralOverlapRootGenerators318 in the trace closure has hash df4db1982626c30c9cacc786f94534e5f2653e74673fd714eb7529dcd6d4be98. I read the diff: it uses an earlier native_overlap_generator proof of actualOverlap_generator rather than the named-carrier overlap_value proof and omits diagnostic #check commands; public definitions and theorem signatures are the same. This does not alter the consumer contract for the two propagated fixes. It is NOT evidence that the older trace proof will elaborate; it may become a later first-error blocker. No replacement of that dependency, Lean result, or whole-closure acceptance is authorized by this review. The central integrator must bind the actual propagated after files and preserve the remaining source differences.
