# Fresh native full-dual sheaf restriction reconstruction

## 1. source_hypotheses

Required: The original normal dual must be localized over the SAME N→O and P→Q scalar maps.

Construction and justification: Consumes the accepted full normal-order linearity producer and retains exact algebra structures; no freeness or arbitrary scalar equivalence is assumed.

Sources: IntegralClosureNativeDualLocalization318.lean

## 2. constructed_objects

Required: Every P-linear valued map O→Q must give an actual Q-linear dual with the original input action.

Construction and justification: Native extendScalarsOfIsLocalization produces Q linearity for each map. Inverse is literal restrictScalars, both evaluation maps are unchanged, and O precomposition linearity is proved pointwise.

Sources: LocalizedValuedDualScalar318.lean

## 3. index_domain_coverage

Required: The source and target are entire finite-dual modules, not selected generators or a proper image.

Construction and justification: OldDual exact identity comparison, native extendScalars.mapIso and the full O-linear localization equivalence give an isomorphism from the ACTUAL ModuleCat extended old dual to all old Q dual.

Sources: IntegralClosureNativeDualLocalization318.lean

## 4. transition_maps

Required: The module-to-sheaf comparison must be the specified native map, not merely a sheaf isomorphism of matching type.

Construction and justification: Uses existing TildePullback318.pullbackIso and its adjunction-unit normalization. Generic hom_formula and adjoint_normalization keep the full native composite explicit.

Sources: NativeTildeLocalizedModule318.lean

## 5. limiting_object_identity

Required: Actual native open restriction requires an actual open-immersion producer.

Construction and justification: Integral closure principal localization yields IsOpenImmersion.of_isLocalization for the literal N→O map. restrictionIso consumes native restrictFunctor and its canonical comparison with pullback.

Sources: IntegralClosureDualNativePullback318.lean

## 6. coefficient_conventions

Required: One-tensors and multiplied inputs must evaluate by the old functional.

Construction and justification: The module composite is reduced through native extendScalars map and exact oldDual identity; one_value and integral_tensor_value retain algebraMap P Q(f(x*n)). No differential factor is inserted.

Sources: IntegralClosureNativeDualLocalization318.lean

## 7. local_conditions

Required: Independent finite and reciprocal actions must be supplied on the actual original charts.

Construction and justification: Finite and infinity application modules use their separate polynomial/Laurent scalars, explicit scalar squares, produced finite presentation and actual normal-order inclusions.

Sources: IntegralNormalFiniteDualSheafRestriction318.lean; IntegralNormalInfinityDualSheafRestriction318.lean

## 8. exceptional_cases

Required: Do not replace old trace lattices or original per-place objects with proxy lines.

Construction and justification: The finite traceRestrictionIso consumes existing traceSheafIso. Infinity uses actual old full reciprocal trace-dual equivalence; OriginalNormalDualNativeRestrictions318 specializes to c,t,w,D and the OLD OriginalNormalInfinityDuality318.dualSheaf. Source domain is constructed from original contact/coefficient facts.

Sources: OriginalNormalDualNativeRestrictions318.lean; IntegralNormalFiniteDualSheafRestriction318.lean; IntegralNormalInfinityDualSheafRestriction318.lean

## 9. downstream_consumption

Required: Native restriction alone does not establish finite/infinity transition or global dualizing/Hodge identification.

Construction and justification: Seven new modules produce separate complete dual restrictions. Reciprocal base transport, overlap trace-coefficient compatibility, differential factor, whole-model gluing and global duality remain separate. All1522 predecessor sources exact.

Sources: README.md; INHERITANCE.json
