# Native pushforward of the actual normalization finite dual

1479 sources: 1475 exact predecessor copies and four new modules. No local Lean or profiling; no resource changes. Kernel acceptance remains hosted and distinct from structural/source review.

The preceding counit packet explicitly stopped at sheafification of the restricted module on the raw affine scheme. This batch constructs the missing NATIVE pushforward comparison. AffineTildePushforward318 first uses pinned pushforwardCompModulesSpecToSheafIso on actual top sections, then the native tilde.isoTop to identify all global sections with the original module under the literal restriction-of-scalars ring map. Native isIso_fromTildeGamma_pushforward and the actual tilde-Gamma counit provide an isomorphism from tilde(restricted M) to the actual Scheme.Modules.pushforward(Spec.map phi)(tilde M). It applies to EVERY module; no freeness, projectivity or finiteness premise is used in that comparison.

IntegralNormalizationFiniteMap318 supplies the literal Spec(intoNormal) map from the actual normalization chart to the raw order. Finiteness is produced from the unchanged localized normal-model theorem and actual denominator, then by Module.Finite.of_restrictScalars_finite through the original raw inclusion. The square with the original source map is proved as a full scheme-morphism equality.

IntegralNormalizationDualPushforward318 uses the actual normal-order finite-dual sheaf with its multiplication-precomposition action, applies the genuine native pushforward along the literal finite map, and identifies that result with the conductor sheaf. It defines the counit first by FULL canonical restriction of functionals, then proves equality with the coefficient counit followed by the original raw perfect frame. The coefficient counit itself factors by the actual conductor inclusion through the produced full sheaf isomorphism. These are entire sheaf morphism equalities, not pointwise rank assertions.

OriginalNormalizationPushforward318 produces the finite map for the original signed finite-place data and records BOTH exact source diagrams: the same Spec(original source)->Spec(normalOrder) enters the SAME proper normal M and the raw-order map used by pushforward. It supplies the native conductor isomorphism for that original chart. The original module coefficient bound is carried through unchanged, with the literal raw different and same M.fieldPoint; no new coefficient frame or scalar is selected.

## Inputs credited and scope

This consumes all of the predecessor's actual conductor range/isomorphism, not a surrogate ideal. Native Tilde and ModuleCat ChangeOfRings primary sources are bound. The tilde pushforward comparison is constructed here from their actual components; no previous global-duality claim is assumed. LocalizedNormalModel finite_normal_model and the exact old raw inclusion provide finiteness. OriginalNormalOrderChart supplies the existing same-model chart/source identity.

## Still not claimed

No infinity-overlap gluing of normal finite duals; no global proper-model duality adjunction or relative dualizing/Hodge identification; no regular-resolution comparison or numerical exceptional divisor; no normal-order/conductor freeness, reciprocal-only place conclusion, KS210 or metric theorem. This removes the AFFINE native-pushforward boundary only. The signed-point bound is explicitly the underlying module coefficient bound, not an unproved pullback-flatness or stalk-fiber exactness assertion.
