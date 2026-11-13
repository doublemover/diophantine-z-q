# Actual overlap model maps

## 1. source_hypotheses

Required: A full dominant source, reduced overlap and actual separated target over the same affine base are required.

Construction and justification: AffineDominantSeparatedExt318 proves dominance from the literal injective ring map and first proves equality of the two base maps before applying relative separatedness. OriginalNormalOverlapChartEquality318 supplies the domain from the actual ambient integral closure and properness from M.proper.

Sources: AffineDominantSeparatedExt318.lean; OriginalNormalOverlapChartEquality318.lean

## 2. constructed_objects

Required: Use both old model charts, the old principal-localization maps, and the same realization M.

Construction and justification: OriginalNormalOverlapChartMaps318 defines finite/infinity as the exact old localization Spec maps followed by OriginalNormalOrderChart318.chart and OriginalNormalInfinityChart318.chart. Both open-immersion instances come from existing producers.

Sources: OriginalNormalOverlapChartMaps318.lean

## 3. index_domain_coverage

Required: Compare all of Spec of the full normal overlap, not merely its field-valued points.

Construction and justification: The source injection has dense image in the entire reciprocal overlap. The reduced-source separatedness theorem proves equality of the two whole scheme morphisms. No full model-intersection coverage is inferred.

Sources: OriginalNormalOverlapChartEquality318.lean

## 4. transition_maps

Required: Keep variance and the exact order equivalence in the actual source square.

Construction and justification: Spec(overlapEquiv) goes from reciprocal overlap to finite overlap; infinitySource followed by this map equals finiteSource by the literal ambient identity. Their composites into M are M.source, proved from both old chart squares.

Sources: OriginalNormalOverlapChartMaps318.lean

## 5. limiting_object_identity

Required: Do not replace the original proper model, source, point or chart by a parallel object.

Construction and justification: The equality lands in the original M.scheme, uses M.structureMap and retains Spec(M.fieldPoint) through signed_point. No alternative center or point is selected.

Sources: OriginalNormalOverlapChartEquality318.lean

## 6. coefficient_conventions

Required: Do not discard the already-produced reciprocal output conversion and differential unit.

Construction and justification: localDual converts the exact accepted chartComparison using native restriction/pullback isomorphisms. Thus its full sigma-output transport and minus-t-squared differential correction are unchanged; the old trace different's fourth-power change is not substituted.

Sources: OriginalNormalOverlapNativeComparison318.lean

## 7. local_conditions

Required: Produce native comparison for actual arbitrary whole-model modules and all morphisms.

Construction and justification: NativeOverlapPullbackComparison318 composes isoWhiskerRight of native pullbackComp, a second pullbackComp, pullbackCongr of the proved square, and inverse pullbackComp. Its native naturality covers every module map. The actual original charts specialize this functor isomorphism.

Sources: NativeOverlapPullbackComparison318.lean; OriginalNormalOverlapNativeComparison318.lean

## 8. exceptional_cases

Required: Keep every finite place and all original coefficient assumptions; do not silently exclude bad primes.

Construction and justification: The c,t,w,D consumer obtains sourceDomain from the old normalized-data/contact/nonzero producers. No restriction on residue characteristic is added, no normal-model regularity is asserted, and no extra local scalar or freeness premise is inserted.

Sources: OriginalNormalOverlapChartEquality318.lean; OriginalNormalOverlapNativeComparison318.lean

## 9. downstream_consumption

Required: A chart-map equality is not full categorical-intersection coverage or effective global descent.

Construction and justification: globalModule is the genuine comparison for a pre-existing arbitrary global module. localDual is the exact old local dual comparison, separately normalized. Equality with a global object's comparison is NOT assumed; full-intersection coverage, trace-form coherence, effective gluing, dualizing/Hodge and regular-model discrepancy remain open.

Sources: README.md; OriginalNormalOverlapNativeComparison318.lean
