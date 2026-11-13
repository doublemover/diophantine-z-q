# Full original normal-chart coverage and intersection

## 1. source_hypotheses

Required: Use the actual normalization section-equivalence chart, not arbitrary open charts with merely dense agreement.

Constructed and justified: NormalizationClosureChartRange318.range unfolds the OLD data constructor: a Spec isomorphism followed by the affine preimage fromSpec. Exact opensRange_comp_of_isIso and opensRange_fromSpec give the full inverse image.

Sources: NormalizationClosureChartRange318.lean; FULL-OVERLAP-PRIMARY/AffineScheme.lean; FULL-OVERLAP-PRIMARY/OpenImmersion.lean

## 2. constructed_objects

Required: Preserve both original normal orders, charts, projection and the same proper-normal realization M.

Constructed and justified: OriginalNormalChartRanges318 consumes the OLD canonicalData for both charts and transports its exact range through OriginalNormalModelCanonicalIso318.iso, using the existing projection compatibility. The finite polynomial-action equality is transported exactly as in the old constructor.

Sources: OriginalNormalChartRanges318.lean; OriginalNormalOrderChart318.lean; OriginalNormalInfinityChart318.lean; OriginalNormalModelCanonicalIso318.lean

## 3. index_domain_coverage

Required: Cover all points of M, including vertical points and every finite place.

Constructed and justified: Each chart range is the entire inverse image of the corresponding standard projective-line chart. JLineAtlas318.standard_opens_cover proves joint surjectivity. The native OpenCover uses these same two maps, and every point of the existing center is covered. No pointwise coverage is upgraded to factorization of the whole center through one chart.

Sources: OriginalNormalTwoChartCover318.lean; OriginalNormalChartRanges318.lean; FULL-OVERLAP-PRIMARY/JLineAtlas318.lean

## 4. transition_maps

Required: Identify the FULL intersection with the actual old normal-order localizations and correct reciprocal variance.

Constructed and justified: IntegralJLineOverlapOpen318 generalizes both surviving projective-chart preimage proofs from Q to any commutative ring. OriginalNormalFullOverlap318 proves the old infinity localization image is exactly D(S), pulls back the full finite chart using the old infinity projection square, and applies native IsOpenImmersion.isPullback. The first leg is j followed by finite i, where j is Spec of the accepted overlap ring equivalence; the second is the old infinity k.

Sources: IntegralJLineOverlapOpen318.lean; OriginalNormalFullOverlap318.lean; OriginalNormalOverlapChartEquality318.lean; FULL-OVERLAP-PRIMARY/OpenImmersion.lean

## 5. limiting_object_identity

Required: Do not substitute a generic model, abstract localization, or unbranched source for the model intersection.

Constructed and justified: The pullback lands in the original M.scheme and uses precisely OriginalNormalOrderChart318.chart and OriginalNormalInfinityChart318.chart. The source is the entire InfinityOverlap integral closure, not SourceOpenRing. The actual range intersection is the old composite k followed by the old infinity chart.

Sources: OriginalNormalFullOverlap318.lean; OriginalNormalOverlapChartMaps318.lean; OriginalNormalOverlapOrderLocalization318.lean

## 6. coefficient_conventions

Required: Retain finite and reciprocal polynomial actions, original coefficients and differential convention.

Constructed and justified: The infinity basic-open element is literally OriginalNormalInfinityOrder318.polynomialScalar X, with infinityNormalAlgebra and infinity_localization installing the old reciprocal action. No dual transition is changed: the exact inherited -T^2 reciprocal correction remains in localDual. Coverage alone does not identify localDual with a global dualizing object.

Sources: OriginalNormalFullOverlap318.lean; OriginalNormalOverlapNativeComparison318.lean; OriginalNormalReciprocalDualTransition318.lean

## 7. local_conditions

Required: Use a complete principal localization, not a punctured subset inferred from density.

Constructed and justified: The proof invokes the prior integral-closure principal-localization theorem through infinity_localization and native PrimeSpectrum.localization_away_comap_range. This is equality of full open subsets, hence native categorical pullback, not only agreement on field-valued points.

Sources: OriginalNormalFullOverlap318.lean; IntegralClosurePrincipalLocalization318.lean; FULL-OVERLAP-PRIMARY/PrimeTopology.lean

## 8. exceptional_cases

Required: Do not remove bad primes or assert regularity from normality.

Constructed and justified: All c,t,w,D,M from OriginalAllPlaceNormalModel318 are retained. No additional noncontact, good-reduction, scalar-unit, freeness, regularity or branch-denominator inversion premise is added. Normalization already supplies the same entire charts at bad primes; the overlap only inverts the relevant base coordinate.

Sources: OriginalNormalChartRanges318.lean; OriginalNormalTwoChartCover318.lean; OriginalNormalFullOverlap318.lean

## 9. downstream_consumption

Required: Record exactly which global duality obligations this removes and which remain.

Constructed and justified: The prior native comparison now has the actual full categorical intersection as domain, and both full normal charts cover M. Effective descent of the local dual modules, ambient trace/differential coherence, identification with a dualizing/Hodge object, regular-model comparison and discrepancy remain unproved. This packet does not alter the canonical 2,000-module audit replay.

Sources: README.md; OriginalNormalFullOverlap318.lean; OriginalNormalOverlapNativeComparison318.lean
