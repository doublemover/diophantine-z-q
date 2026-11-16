# Independent geometry source review, run 43539970197

Published head 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b. No source-level blocker found in the two exact candidates below. No local Lean/Lake was run. Hosted compilation, declaration audit and whole-packet acceptance remain pending.

## IntegralRationalInfinityMap318

Before3865fb8833b519894da943be3239ce57f2326136be6728a88e3c5eb9f90fe17c; after868e4abf61f8ef5ec9840296b83871789ab7102eccd6e2e283a52a1d349a07fa. Center-r59 artifact14092475540, exact log b698cd2c1464926c5101acf25480f2c9c20d406156331728307620f704df7e50; module failed12.092 seconds. The sole error is application of rational_infinity_comp_ext to the concrete maps, with hidden OreLocalization.instAdd obstructing type unification.

The replacement private rational_infinity_ext accepts two already-constructed ring homomorphisms from the same exact infinity order to one arbitrary commutative target. It does not synthesize another algebra structure on an intermediate overlap. The public field_restriction still passes literally (originalFieldEmbedding c).comp (infinityMap ℚ c).toRingHom and originalEmbedding c. The conclusion, input units and actual field/overlap maps are unchanged.

The helper delegates to the same full rational_order_ext: rational constants by RingHom.ext_rat, the entire localized polynomial base by localization extensionality, and every one of the three ordered root generators. It is not merely checking a generic point or one generator. The actual coordinate/root witnesses are unchanged; only RingHom.comp_apply and AlgHom.coe_toRingHom normalize application of the already-built composite. The latter theorem was independently verified in pinned Mathlib Algebra/Algebra/Hom.lean at56a005855ea17e0b0958f73ec801ae140b0a1679 and saved as primary/AlgHom.lean. No new compatibility hypothesis, algebra action, scalar factor or field component is substituted. The downstream full infinity_restriction still uses original open-embedding injectivity and is byte-identical. Whether this removes the concrete unification failure is a hosted question.

## LocalizedTensorRestriction318

Before3854c2f1dcf457725c04d69057f455ea57edd32d49431c890ceaa5c471700332; final after41c9c0cf6189e6f44df26cbfe582d9d4a35398fb49b2cb0721ae76aed2f63ba0. Lattice-r10 artifact14092231758, exact log76a8ddf4208927220089ccdca5d0eca2837224dcfee985dcdd02fd63f5efd182; module failed1.568 seconds. The earlier named/typed target algebra no longer triggers its original instance declaration failure. Current errors instead infer ℕ from an untyped tensor1, leave the localization L metavariable unresolved, and fail to match the native lift_tmul through the toRingHom view.

Both evaluation statements now explicitly bind the existing arbitrary localization L on lift, and lift_right types its1 as L. This restores the intended general localized tensor statement rather than a Nat specialization; literal statement-text invariance is not claimed. The actual lift, baseMap, rightMap and targetAlgebra definitions are unchanged. Target action remains exactly (f.comp(algebraMap A B)).toAlgebra, explicitly installed at Algebra A T, with only the original assumption that f(algebraMap A B x) is a unit.

The proof changes only the view of the same map to its native Algebra.TensorProduct.lift application. Pinned Maps.lean lift_tmul gives baseMap l * rightMap b. The right equation then uses map_one/one_mul and the literal rightMap=f. The left equation uses map_one/mul_one and the exact baseMap.commutes a; with the named target action its right side is f(algebraMap A B a), not an arbitrary scalar action. Source and target remain the full L tensor[A] B and T. The current consumer IntegralOriginalCommonRestriction318.commonRestriction already fixes L:=Laurent R and uses the same finiteRestriction and original invertible root; common_finite consumes the intended general lift_right equation. No point, generator family or localization hypothesis is removed.

Final right proof uses simp-only followed by <;> rfl to avoid a no-goals failure; the superseded d2c348 draft is not the reviewed target. All imports, resource options and trust settings are unchanged.

## Evidence

Both .before files independently match their own published predecessor sources. Own center/lattice RESULT packet hashes match exact published intake ded7d9ac6f0b793132b1f7643df27999711e011658be03efc37bce520d1e83b7 and923023ea349e6979416331268283ca7fdbf07d532ef093c996e368b6993ae429, respectively. Full exact logs, before/after/diffs and own results were read. The entire mathematical application remains the original chart and tensor-localization maps. No local compiler success or independent mathematical acceptance is inferred from these source checks. Successor propagation requires a separate byte/contract review.

Pinned Mathlib evidence hashes:
- AlgHom.lean: 839f7471fed0a18fbe9d132c70eee788f5003e621ba59e649c8d7ea7bfbc34d8
- LocalizationAwayBasic.lean: d651befeb3c6909a1e5d6359c6a9e7996c4eec31187552dc2652d93fe30823b8
- TensorProductMaps.lean: 098a8f3c35f76da90d9a8646ccab8280f0e7a941d9a5ce9c6d17f9fa51627753
