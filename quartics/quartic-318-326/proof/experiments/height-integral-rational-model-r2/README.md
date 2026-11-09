# Actual integral model and original rational normalization

Identify the actual integral two-chart pushout specialized to Q with the original global contact normalization, using the exact signed finite and infinity restriction maps, full categorical intersection and original Q-structure morphism.

## Scope

This connected 43-source packet has 37 unchanged predecessors, three exact reused producers, and three new modules. It constructs the full rational scheme isomorphism, not only a common-field or generic-open comparison. Both original chart maps and the Q-structure morphism are retained. It does not assert an arbitrary-base-change comparison, bad-prime regularity, all-place lattices, PEL realization, the final height bound, or the full arithmetic theorem. Functorial identification of the integral bicanonical pair with the original global sections remains a separate consumer.

## Source-to-consumer comparison

1. **Objects.** Required: Source and target must be the actual original schemes and ring maps. Constructed: Source is IntegralGluedModel.scheme Q c, target is ContactGlobalSmooth.Model c. Chart maps are spectra of the exact source, overlap and infinity algebra equivalences, not abstract chosen affine isomorphisms. Evidence: IntegralRationalGlobalComparison318.finiteIso; infinityIso; overlapIso; originalModelIso.

2. **Index and chart coverage.** Required: All original root generators and every point of the global scheme must be covered. Constructed: Every Fin3 infinity ratio generator is tracked with original label j.succ. The full original Bool finite/infinity cover is used to construct the inverse. Both inverse laws use whole-chart hom extensionality. Evidence: IntegralOtherRootCoordinates318.regroup_other; IntegralRationalInfinityMap318.field_restriction; IntegralRationalGlobalComparison318.from_to.

3. **Coefficients and exceptions.** Required: Integral identities must not require a square-root choice or extra domain assumption. Constructed: Signed finite-root identities hold over arbitrary commutative R and four units. Rational field comparison specializes exactly R=Q and uses the already constructed original source field and its injective open embedding. No new exceptional prime claim is made. Evidence: IntegralOtherRootCoordinates318.common_other; IntegralRationalInfinityMap318.infinity_restriction.

4. **Transition maps.** Required: Both atlas squares must commute on the complete overlap. Constructed: The finite square was proved through the whole original quartic localization. The infinity square is now proved by localized polynomial-base extensionality plus all three actual generators, then injectivity of the original field embedding. Evidence: IntegralRationalInfinityMap318.field_restriction; infinity_restriction; IntegralRationalGlobalComparison318.infinity_inverse_square.

5. **Scalars and signs.** Required: Preserve u=c0/y0 and each signed root quotient y_j/y0. Constructed: The actual rootUnit inverse, original finite generator j, and original signed source root j.succ are mapped through the same field embedding. Ratios are never identified merely from their squares. Rational structure commutes by the actual chart scalar maps. Evidence: IntegralRationalInfinityMap318.generator_original_field; IntegralRationalGlobalComparison318.over_Q.

6. **Identity and gluing.** Required: A comparison on a dense open does not identify the global normalization. Constructed: The map out of the original integral pushout is defined by pushout.desc. Its inverse is glued across the full original normalization cover using ContactFullOverlap.actual_pullback. Both compositions are the identity; originalModelIso packages them. Evidence: IntegralRationalGlobalComparison318.backward_compatible; toOriginal; fromOriginal; to_from; from_to.

7. **Consumer.** Required: Retain the original finite and infinity embeddings and base map downstream. Constructed: Exact finite_toOriginal and infinity_toOriginal formulas identify the original chart embeddings. over_Q proves equality with the original normalization structure morphism, so this is a comparison of the original rational models over Q. Evidence: IntegralRationalGlobalComparison318.finite_toOriginal; infinity_toOriginal; over_Q.

8. **Remaining obligations.** Required: Do not infer arithmetic regularity or integral heights from rational scheme identity. Constructed: The original global bicanonical sections still need explicit functorial attachment to the integral glued tensor pair, and bad-prime regularity, actual all-place DVR/frame production, PEL and metric-height comparison remain open. This is specialization of the explicit ring construction to Q, not an unproved arbitrary-base-change theorem. Evidence: README.md scope; ContactGlobalBicanonical318.

9. **Validation and history.** Required: Require exact evidence and independent review before acceptance. Constructed: Thirty-seven predecessor sources are unchanged; two signed-generator helpers are copied from the proper-model author and one original-infinity comparison from hosted-passed infinity-r5. The three new consumer files are statically checked and remain pending hosted Lean and independent review. No local Lean or accepted-baseline modification. Evidence: verification/predecessor-source-pins.json; verification/reused-producer-pins.json; verification/baseline-source-pins.json.

## Validation

No local Lean was run. Static import order, hashes and source policy pass with 224 baseline dependencies. Hosted compilation, recursive axiom audit and independent mathematical source review are pending. The accepted 1837-module baseline remains unchanged.

## Exact hosted 1ca04ec repair

Repair the four shared CommonBase elaboration failures from hosted 1ca04ec: normalize the actual mapped scalar coercion before ring normalization, explicitly rewrite the original R[X] and R scalar towers before reducing contact zero, use the pinned isUnit_of_mul_isUnit_left theorem, and supply the exact denominator unit proof to Away.lift_eq. The original root, reciprocal relation, twists, polynomial coordinate, maps and all theorem statements are unchanged.

The tested packet height-integral-rational-overlap-r1 and all prior frozen source bytes are preserved. Direct quadratic root scaling now passed hosted CI. Exact RESULT and failing source log are preserved in previous-ci-failure/1ca04ec. No local Lean was run; revised hosted verification and independent acceptance remain pending.
