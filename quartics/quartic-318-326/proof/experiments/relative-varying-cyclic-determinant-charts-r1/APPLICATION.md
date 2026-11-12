# Application contract: Construct normalized maps on the full determinant cover

1. **source_requirements.** Required: Build local classifying maps from a general cyclic action, without assuming a global word basis.

Constructed: All actual determinant localizations and their mapped cyclic actions are constructed.

Justification and boundary: Every word tuple is retained and determinants_span_top supplies the full Spec S cover.

2. **constructed_objects.** Required: Normalization must act on the original tensor-source quotient frame.

Constructed: frame_columns identifies the actual evaluation matrix with the literal original source-word columns.

Justification and boundary: normalize uses that exact unit determinant and framed_point verifies the same normalized action/vector after the represented point equivalence.

3. **index_coverage.** Required: Cover all coefficient rings and all determinant opens.

Constructed: Arbitrary commutative R-algebra S and every word tuple, including zero localizations and empty finite index.

Justification and boundary: The actual affineOpenCoverOfSpanRangeEqTop uses exactly delta and the original cyclicity-generated unit ideal.

4. **transition_maps.** Required: Coordinate maps and coefficient structures must be actual ring/scheme morphisms.

Constructed: coordinate is the inverse normalized-point equivalence; schemeMap is Spec of that R-algebra map followed by the real glued chart inclusion.

Justification and boundary: over_base verifies the exact original parameter structureMap, not an abstract point or untyped set map.

5. **hypothesis_checks.** Required: Determinant localization must have a proved invertibility witness.

Constructed: unit transports determinant_map through the actual localization algebra map and uses Away.algebraMap_isUnit.

Justification and boundary: localized is the genuine all-ring mapCyclic, so no surjectivity or flatness assumption is silently added.

6. **consumer_identity.** Required: The local point must classify the original full ideal, not only a frame-equivalent vector space.

Constructed: ideal_point follows from actual frame normalization preserving toIdeal; local_ideal composes it with arbitrary coefficient ideal_map.

Justification and boundary: The final ideal is literally Ideal.map of the original S tensor A kernel under the localization tensor map.

7. **normalizations.** Required: Preserve source/scalar choices and nilpotents.

Constructed: All655 predecessor sources exact; local ideal equality is in the entire localized tensor-source ring.

Justification and boundary: No radical, geometric-point test, change of source algebra or rank-only substitution occurs.

8. **downstream_boundary.** Required: Local maps do not by themselves give a global classifier.

Constructed: A full actual determinant cover, actual local normalized maps and exact local ideal recovery are supplied.

Justification and boundary: Overlap compatibility, gluing, frame independence and correct locally-free versus globally-free global classification remain separate.

9. **evidence_acceptance.** Required: Independently compare exact producers and consumers.

Constructed: Two new modules and exact655 predecessor, primary localization/open-cover/normalization APIs and static checks.

Justification and boundary: Fresh bounded source/application review and hosted kernel acceptance remain distinct; no local Lean or profiler.

