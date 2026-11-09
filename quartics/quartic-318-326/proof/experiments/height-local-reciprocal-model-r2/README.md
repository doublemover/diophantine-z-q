# Whole normalized reciprocal models at coefficient places

Construct full finite and reciprocal four-root orders for arbitrary integral coefficients, their genuine full-overlap gluing and finite projective projection, and produce original signed valuation-ring chart points after one actual twist normalization at every coefficient place.

This83-source candidate retains68 predecessor sources, reuses the exact unit-free quadratic scaling producer and adds14 modules. The new whole model permits nonunit normalized twists and retains all ramification points. Its projective coordinate is the original t, with w=1/t at infinity; all four roots scale by t on the full overlap. It is potentially singular.

The valuation-ring consumer chooses one common normalization before the finite/infinity dichotomy and constructs genuine chart ring maps recovering all original signed roots. It does not yet identify a global generic point with the original smooth model, or prove bicanonical extension across the new singularities. Those are explicit next joins.

## Source-to-consumer obligations

1. **Arbitrary coefficients and full source.** Required: Do not impose unit twists or invert radicands to avoid excluded places. Constructed: The finite order has yi²=di*(t−ai); the whole infinity order has vi²=di*w*(1−ai*w), for arbitrary coefficients di,ai in R. Both are full finite free four-root polynomial orders. Evidence: DVRNormalizedFiniteOrder318; DVRNormalizedInfinityOrder318.

2. **Actual original local roots.** Required: The infinity chart must recover the original signed point, including nonintegral t. Constructed: At each DVR, one simultaneous twist normalization is chosen before the t-integrality dichotomy. Finite roots are yi/si; reciprocal roots are yi/(si*t), with w=1/t. Every original root is recovered exactly, including zero contact roots. Evidence: DVRNormalizedAllPlaceCharts318.chart_center.

3. **Full coefficient localization.** Required: The common coefficient ring must be the entire punctured base in both directions. Constructed: The actual Laurent ring R[t,t^-1] is a principal localization under both its canonical and its reciprocal w=1/t scalar action, proved through the explicit involution and native localization witnesses. Evidence: NormalizedReciprocalLaurent318.reciprocal_localization.

4. **Signed full-order comparison.** Required: An equality of radicands alone is insufficient. Constructed: The literal parameter identity finite_i=infinity_i*t² yields a genuine four-root order equivalence scaling every signed generator by t. Radicands may vanish; only the common coordinate is a unit. Both sides are actual scalar extensions of the whole orders. Evidence: FourRootUnitScale318.four_generator; NormalizedWholeOverlap318.fullOverlap; finiteBaseChange; infinityBaseChange.

5. **Actual scheme gluing.** Required: Both overlap maps must be genuine open immersions with the full intersection. Constructed: Each order map is a scalar base-change principal localization followed by the explicit order equivalence. The resulting pushout has both original affine chart inclusions, full point coverage and categorical pullback intersection. Evidence: NormalizedWholeOpenMaps318; NormalizedWholeGluing318.intersection_square.

6. **Original projective coordinate.** Required: The projection must use the same t and reciprocal1/t, not auxiliary root coordinates. Constructed: Exact polynomial-map identities yield the unit-overlap relation for the original projective line charts. The glued map uses literal t on the finite chart and w on the reciprocal chart; no twist unit coordinate scaling is used. Evidence: NormalizedWholeScalarMaps318; NormalizedWholeProjection318.projection.

7. **Entire target preimages and properness.** Required: Affine pieces over a target chart do not alone prove a finite morphism. Constructed: Exact source-open ranges and target chart intersection formulas prove that each full order is the ENTIRE target-chart preimage. Actual ring finiteness gives a finite projective projection and hence proper and separated structure map. Evidence: NormalizedWholeProjectivePreimages318; NormalizedWholeProjectiveProper318.proper_separated.

8. **Geometric and height boundaries.** Required: A proper potentially singular model is not a regular normalization or a section-lattice realization. Constructed: No normality, reduced-fiber or regularity assertion is made. The generic-fiber normalization identification with the original smooth projective model, extension of original bicanonical sections and excluded-place height bounds remain open. The chart-center theorem gives actual maps/root identities, not yet an equality of global generic scheme points on this new model. Evidence: README.md; DVRNormalizedAllPlaceCharts318.chart_center.

9. **Prior arguments and validation.** Required: The revised4-root application requires its own coverage and scalar checks. Constructed: The earlier3-root good-base whole-order argument is pinned and read directly. The new route changes to four roots, arbitrary nonunit coefficients and canonical reciprocal target coordinates; all transition/entire-preimage proofs are included. All68 immediate predecessor sources are unchanged. Static and symbolic checks do not certify Lean or the arithmetic theorem. Evidence: verification/consumer-source-pins.json; verification/predecessor-source-pins.json.

## Validation

Static source/import policy:83 modules and248 baseline dependencies. Exact reciprocal parameter and root-rescaling identities checked symbolically. No local Lean. Hosted kernel/recursive audit and independent bound review remain pending. Accepted baseline unchanged.

## Exact current hosted repair

Replace the unscoped R[X] coefficient type by explicit Polynomial R in the actual localization call. This namespace does not open Polynomial, so the reported unknown X is inside that type notation; the element is already explicitly Polynomial.X. No proof statement, map, hypothesis or900k budget changes.

The tested packet height-primitive-chart-norms-r2 and earlier frozen bytes remain preserved. The preceding BaseEquiv producer now passed hosted checking. Exact RESULT and failing source log are retained under previous-ci-failure/bbf417b-replay. No local Lean was run. Hosted kernel outcome and independent acceptance remain pending.
