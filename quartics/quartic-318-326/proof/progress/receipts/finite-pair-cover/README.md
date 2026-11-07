# Actual four-chart cover of finite-point pairs

The exact four relative addition chart functions generate the unit ideal in the actual tensor coordinate algebra of two finite Weierstrass points:

1. `RelativeChordAlgebra318.gap` (ordinary chord),
2. `TangentOpenAlgebra318.ordinateSum` (complementary tangent/secant),
3. `InfinityAdditionAlgebra318.numeratorY false` (inverse output at infinity),
4. `InfinityAdditionAlgebra318.numeratorY true` (two-torsion doubling output at infinity).

The only generic premise is that the actual short-Weierstrass discriminant is a unit. The unit property of 2 is derived, not assumed separately. For the literal OpenJ coefficients no premise remains.

The proof works over every domain-valued point of the actual tensor algebra. If the first two functions vanish, the abscissae agree and the ordinates are opposite. Vanishing of the first homogeneous ordinate numerator forces the input ordinate to vanish. Vanishing of the second forces `3*x^2+A=0`. The actual input equation then gives `A=-3*x^2`, `B=2*x^3`, contradicting the discriminant unit. Applying this to each actual prime quotient proves the four basic opens cover, hence their functions span the unit ideal.

`FinitePairSchemeCover318.productCover` is an actual `Scheme.OpenCover` of the relative affine self-fiber-product over the original base. Its four structure morphisms are proved definitionally equal to the existing ordinary-chord, tangent, and two infinity-output chart maps. This is not only a field-point coverage assertion.

Reproduce with `bash build.sh`: Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, strict kernel checking and recursive axiom audit. Dependencies are listed in `run-one.sh`.

Boundary: this establishes coverage for two finite inputs. Compatibility/gluing of addition chart maps, inputs at infinity, complete relative group laws, multiplication/torsion and the full refined global realization are separate tasks. It assumes none of those conclusions.
