# Fresh reciprocal-base full-dual transport

## 1. source_hypotheses

Required: Both scalar algebras and an actual commuting pair of ring equivalences are needed; equal carrier types or degrees do not suffice.

Construction and justification: ScalarChangedFiniteDual318 retains separate R→A and S→B algebras, sigma and e, and the explicit pointwise scalar square h; inverse_scalar is proved from h and injectivity.

Sources: ScalarChangedFiniteDual318.lean

## 2. constructed_objects

Required: Transport every functional, with the original multiplication-precomposition order action.

Construction and justification: The map is sigma(f(e.symm b)), inverse sigma.symm(g(e a)). Additivity, scalar linearity, both inverse laws, and entire-order semilinearity are proved. The old Dual carrier is used directly.

Sources: ScalarChangedFiniteDual318.lean

## 3. index_domain_coverage

Required: Use all dual inputs, not basis generators or assumed trace representations.

Construction and justification: No finite-rank, freeness, or trace representability hypothesis is used in generic transport. Native restrictedIso covers the entire old dual; native ring-equivalence restriction is an equivalence, making its adjunction counit an isomorphism.

Sources: ScalarChangedDualNativeExtension318.lean

## 4. transition_maps

Required: Native scalar extension and sheaf pullback must keep the actual counit and Tilde normalization.

Construction and justification: extensionIso is extendScalars.mapIso(restrictedIso) followed by asIso of the actual extend/restrict adjunction counit. one_value and integral_tensor_value identify it pointwise. The old TildePullback comparison is composed with this same module isomorphism.

Sources: ScalarChangedDualNativeExtension318.lean; NormalOverlapReciprocalDualSheaf318.lean

## 5. limiting_object_identity

Required: The two integral overlap rings must be the old closures under their independent Laurent scalar maps.

Construction and justification: Uses IntegralOriginalNormalOverlap318.overlapEquiv, which is literally identity in the common OpenOrder, and its scalar_square with the full Laurent involution. Both scalar subtype algebras are explicit. Existing old finite/infinity overlapDual objects are consumed.

Sources: NormalOverlapReciprocalDual318.lean; NormalOverlapReciprocalDualSheaf318.lean

## 6. coefficient_conventions

Required: Keep reciprocal output conversion and the exact differential sign/power distinct from trace-denominator scaling.

Construction and justification: The raw dual transport includes tau on outputs. The separate unit is finite −T², sent along the actual order equivalence. factor_ambient is −t² in the original source; reciprocal_value is −S⁻² times tau(f z). No t⁻⁴ trace-denominator equality is substituted.

Sources: NormalOverlapDifferentialDualTransition318.lean

## 7. local_conditions

Required: Retain the original signed point's coefficient data and actual previous chart restrictions.

Construction and justification: OriginalNormalReciprocalDualTransition318 consumes c,t,w,D, the old finite traceSheaf restriction, and OLD OriginalNormalInfinityDuality318.dualSheaf restriction using the previously produced native isomorphisms.

Sources: OriginalNormalReciprocalDualTransition318.lean

## 8. exceptional_cases

Required: Do not assume invertibility, finite presentation or a chosen frame beyond the available producers.

Construction and justification: The scalar transport works for arbitrary commutative rings; both differential factors are actual units, built from the actual Laurent coordinate unit. Original trace restriction uses the old domain/nonzero/contact producers through the accepted exact native restriction checkpoint.

Sources: NormalOverlapDifferentialDualTransition318.lean; OriginalNormalReciprocalDualTransition318.lean

## 9. downstream_consumption

Required: A comparison isomorphism does not automatically prove its compatibility with ambient trace forms or the model's categorical intersection.

Construction and justification: chartComparison is explicitly the old finite restriction followed by actual reciprocal module/sheaf transition and old infinity restriction inverse. comparison_infinity proves its normalization. Full categorical intersection, trace-form equality, whole-model gluing, global duality/Hodge, regularity and discrepancy remain unproved here.

Sources: README.md; OriginalNormalReciprocalDualTransition318.lean
