# Genuine tangent-fiber quadratic forms

This packet identifies each actual differential-orbit fiber on the Γ1(N) complex manifold (N ≥ 5) with genuine continuous complex bilinear forms on the Mathlib tangent fiber.

`TangentCoordinates318` binds the actual `tangentBundleCore` and its actual local trivializations to the complex derivative of the genuine quotient-chart transition. `ComplexQuadraticForms318` proves that every continuous bilinear form on the complex line is determined by its value at (1,1), yielding the exact coefficient equivalence and symmetry. `ActualQuadraticForm318.quadraticEquiv` and `quadraticHomeomorph` compose these with the already registered actual orbit fiber structure.

The decisive geometric statement is `chart_evaluation`: pairing the actual coefficient in any quotient chart with two actual tangent-trivialization coordinates returns the same bilinear form. The inverse derivative-square factor cancels the two actual tangent derivatives; their nonvanishing is proved, not assumed. Thus the interpretation is chart-independent, not merely an unrelated one-dimensional linear isomorphism.

The last equivalence is continuous in each actual fiber. A global morphism between the registered line bundle and the iterated Hom bundle, the analytic/algebraic Kähler-sheaf comparison, and cusp/source compactification remain separate. No claim about these later identifications is made here.

Replay `bash build-all.sh`. Strict kernel checking is enabled for every declaration; permitted roots are only propext, Classical.choice and Quot.sound.
