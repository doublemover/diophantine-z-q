# Application contract: Glue original projective quotient ideals

1. **source_requirements.** Required: Use the actual complete projective source charts and overlap.

Constructed: ContactOriginalRelativePolynomialCharts and ContactOriginalRelativeOverlap supply the original R tensor finite/infinity/Laurent rings and maps.

Justification and boundary: The full intersection theorem plus injectivity of the actual open immersion produces a categorical pullback, not a punctured or field-only overlap.

2. **constructed_objects.** Required: Compatible local quotient data must retain entire ideals.

Constructed: Datum contains arbitrary finite-chart and infinity-chart ideals and equality of their literal ideal extensions under the actual ring arrows.

Justification and boundary: The overlap ring quotient uses that exact common ideal, not its radical, support or a same-rank module.

3. **index_coverage.** Required: All local comparisons must cover the entire global source and quotient.

Constructed: The actual original two-chart cover is retained; the open pushout charts jointly cover by pinned locally-directed colimit surjectivity.

Justification and boundary: The original overlap is the categorical intersection of the glued quotient charts, proved from exact colimit identifications.

4. **transition_maps.** Required: Gluing maps must agree and local quotient charts must be actual base changes.

Constructed: AffineQuotientPushout produces both overlap squares; genuine open maps give a scheme pushout. Scheme.isPullback_of_openCover plus original and quotient intersection squares recover each chart.

Justification and boundary: All transition data come from the original quotient ring maps. No abstract descent assertion replaces these actual squares.

5. **hypothesis_checks.** Required: Do not assume local finite/free quotients incorrectly.

Constructed: Only commutative coefficient Q-algebra and compatible arbitrary full ideals are required.

Justification and boundary: A moving finite-flat projective divisor may have nonfinite open chart restrictions, so no chart-wise finite/free hypothesis is inserted; whole-family finiteness/flatness remain separate.

6. **consumer_identity.** Required: Global object must be a closed quotient of the actual original curve.

Constructed: The pushout maps to the unchanged p-first relative Contact curve. Closedness descends through actual full finite/infinity Cartesian models.

Justification and boundary: This consumes the original ContactProjectiveModel-derived family, not a separately chosen curve or only the source affine chart.

7. **normalizations.** Required: Ideal sheaf and variance must be exact.

Constructed: The global ideal is the kernel of the original closed immersion; its subscheme comparison is actual toImage. Kernel pullback identities recover both original full chart kernels.

Justification and boundary: No radicalization or equality only of underlying sets is used.

8. **downstream_boundary.** Required: Identify the projective/Jacobian boundary.

Constructed: Compatible arbitrary full chart ideals now glue to an actual global closed subscheme with exact chart recovery.

Justification and boundary: Global finite-flat bounded-degree conditions, effective Cartier regularity, O(D), projective quotient moduli, Abel/Picard and Jacobian identification are not claimed.

9. **evidence_acceptance.** Required: Fresh source/API/consumer review and hosted checking.

Constructed: Eight new full bodies over exact694r2; pinned locally-directed gluing, original charts, affine quotient, local closedness and ideal-sheaf functorial APIs.

Justification and boundary: Static/source review is separate from kernel acceptance. No local Lean/profiler, cap increase or acceptance bypass.

