# Actual dimension of the integral j-model

Fresh strict kernel replay and exhaustive recursive axiom audit pass for six declarations in two modules. The only axiom roots are `propext`, `Classical.choice`, and `Quot.sound`.

`IntegralDimension318.dimension_eq` derives preservation of actual ring Krull dimension under an integral injective extension. It uses actual prime-spectrum incomparability and going-up chain lifting, not a supplied dimension equality. The integer polynomial ring has dimension exactly two.

`JModelDimension318.chart_dimension_two` applies this result to both actual affine chart rings of the previously constructed proper normalization. The section-ring/integral-closure identification is the checked `NormalChart318.sectionsEquiv`. Injectivity of both finite and reciprocal polynomial maps is derived from the literal localization, the reciprocal equivalence, and finite-etale flatness.

Inputs are a positive level (expressed as `N != 0`) and an actual domain finite-etale algebra B over the literal open-j base. The two chart rings belong to that same proper, normal, Noetherian, flat, surjective model; they are not independently chosen orders.

This proves the affine dimension assertion, not regularity or semistability. It does not construct the particular modular or PEL cover algebra/component, a resolution, a canonical or Hodge identification, or the global Arakelov realization. No unconditional FiveContact49Height theorem is asserted.

Run `bash build.sh`. Frozen files are exactly the receipt whitelist and the receipt/manifest; exploratory logs and compiled artifacts are excluded.
