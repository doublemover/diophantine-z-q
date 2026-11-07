# Global holomorphic quadratic-form bundle equivalence

For N ≥ 5, this packet identifies the actual registered differential-orbit line globally with Mathlib's genuine iterated Hom bundle `TangentSpace →L (TangentSpace →L ℂ)` on the constructed complex Γ1 quotient.

`FormBundleCoordinates318.form_coordinates` proves the exact coordinate identity in the standard Hom-bundle trivialization. It evaluates the actual quadratic form on the two actual inverse tangent trivializations and uses the proved chart-independent pairing. The target topology and bundle are the standard iterated `Bundle.ContinuousLinearMap` constructions, not a transported replacement topology.

`QuadraticBundleEquivalence318.formMap_holomorphic` and `inverse_holomorphic` prove both directions holomorphic using that exact coordinate identity. `formHomeomorph` is the resulting genuine global homeomorphism; base projection, addition and complex scalar multiplication are preserved. Thus the prior fiberwise interpretation is upgraded to a global holomorphic bundle identification.

An algebraic tensor-product presentation of the bilinear forms, comparison with algebraic Kähler sheaves, cusp extension and the specified global arithmetic/PEL model remain separate. The geometric Poincaré tangent-metric/operator-norm interpretation is not claimed by this packet.

Replay `bash build-all.sh`. All declarations are checked by the Lean kernel with `-Ddebug.skipKernelTC=false`. Only propext, Classical.choice and Quot.sound are permitted. Mathlib's unchanged official Hom dependencies were obtained through the official cache (four files).
