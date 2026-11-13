# Native all-open rational values and exact restriction join

## 1. source_hypotheses

Required: Native generic-field transport requires integral source/target and nonempty opens.

Constructed: The actual original integrality producer is used. The generic point proves the whole preimage of every nonempty ambient open is nonempty. The inverse actual open-immersion generic-stalk equivalence, not an arbitrary field isomorphism, defines evaluation.

## 2. constructed_objects

Required: Values must be defined on the original global root ideal sheaf.

Constructed: coefficientMap is the actual old affineProjection composed with affineIdealRestriction. The common-chart local value uses the old affineValue and actual common-chart generic field.

## 3. index_domain_coverage

Required: Comparison must cover every section over every nonempty ambient open, not only top, generators, or marked points.

Constructed: OpenAdjointSections restrictSection is the actual adjunction unit at arbitrary U. Its formula is exactly M.presheaf.map(image_preimage_le). adjoint_apply evaluates the native homEquiv_unit equality at every section. value_square specializes this whole square to the original sheaf.

## 4. transition_maps

Required: Native module restriction and scalar maps must remain intact.

Constructed: PushforwardRationalValue uses forward PresheafOfModules.naturality_apply and native Hom.app_smul. The pushforward scalar is j.app(U)(a), then ambient generic-field compatibility gives multiplication by the original ambient germ. The prior draft mistakenly invoked map_smul on an Ab map and has been corrected before review.

## 5. limiting_object_identity

Required: Separate global and overlap values must be identified by an actual native square.

Constructed: coefficient_square uses the exact old affineValue adjunction and coefficientMap, without an added compatibility hypothesis. value_square identifies generic values after that exact native restriction; eq_iff_section uses the already-produced actual overlap frame injection.

## 6. coefficient_conventions

Required: The inverse-u factor, its restriction, and the old frame must be retained.

Constructed: OriginalOverlapRationalFrame.infinity_formula preserves the literal restricted inverseUSection and actual field maps. No sign is changed and no abstract generator is substituted.

## 7. local_conditions

Required: Full overlap image must not follow merely from injection or a chosen scalar.

Constructed: OverlapValueImage.full_image uses the bijectivity of the actual old affineValue component on each nonempty common-chart open. Thus every regular-function germ occurs, and only such germs occur. RationalImageBound transports each actual global value into this entire overlap regular image.

## 8. exceptional_cases

Required: Do not assert a value on an empty open or discard the n=0 case silently.

Constructed: Every rational-value statement explicitly requires Nonempty U; no totalization on empty opens is claimed. The generic-field and overlap statements add no n nonzero condition. Existing root-principal or nonsingularity statements in the predecessor retain their own n nonzero hypotheses.

## 9. downstream_consumption

Required: Do not turn overlap injection into global sheaf embedding or global lattice exhaustion.

Constructed: AdditiveImage records a genuine range, additive structure, ambient scalar closure and literal image inclusions under restriction. injective_iff_restriction exposes exactly the remaining global restriction injectivity obligation. Global full image, root/infinity intrinsic-stalk identity, associated-divisor/theta/Weil, empty-open packaging and kernel elaboration remain open.
