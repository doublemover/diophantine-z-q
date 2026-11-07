# Genuine point-law interpretation of glued finite-input addition

`FiniteAdditionPoints318.actual_add` proves that the already constructed global finite-input addition Scheme morphism evaluates to Mathlib's genuine Weierstrass group addition on every field-valued pair of finite input points of the literal OpenJ family.

The output is read by the exact completed Scheme field-point equivalence, not by an unspecified bijection. `outputSchemePoint` is explicitly the composition of the actual Spec map of the pair-coordinate algebra homomorphism with `FiniteAdditionGluing318.coordinateAddition`. The input points are read from the two genuine tensor-factor maps.

The proof uses the exact chart restriction of the already glued morphism. If the abscissa difference is nonzero, it lifts to the chord localization. Otherwise it uses the nonzero ordinate sum, when present. If both vanish, the checked discriminant contradiction guarantees one homogeneous ordinate numerator is nonzero, and the corresponding actual infinity-output chart has zero denominator. Those branches give precisely actual inverse-pair addition or two-torsion doubling. All four previously proved local group-law statements are consumed, with no supplied final point-law assumption.

`lift_input` proves equality on the original pair algebra for each actual localization lift. `completed_finite_reading`, `chord_output`, `tangent_output` and `infinity_output` bind every chart's output to the exact completed interpretation.

Reproduce with `bash build.sh`. Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, strict kernel replay and recursive standard-axiom audit. Dependencies are listed in `run-one.sh`.

Boundary: input-at-infinity extension, complete relative group-scheme laws, multiplication/primitive-torsion geometry and full refined global realization remain separate. This packet does not infer Scheme morphism equality from pointwise equality; the actual morphism and its ring-level gluing were already constructed in the preceding packet.
