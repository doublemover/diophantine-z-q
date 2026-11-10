module
public import RelativeOriginalPolynomialAlgebra318
public import Mathlib.Algebra.Module.FinitePresentation
public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace RelativePolynomialFinitePresentation318
open Polynomial
open scoped TensorProduct
universe u
variable (k R B : Type u) [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra (Polynomial k) B]
  [IsScalarTower k (Polynomial k) B]
attribute [local instance] Polynomial.algebra

/-- Finite presentation survives the actual polynomial coefficient
pushout, over arbitrary coefficient rings, not just Noetherian ones. -/
instance original [Module.FinitePresentation (Polynomial k) B] :
    Module.FinitePresentation (Polynomial R) (RelativeOriginalPolynomialAlgebra318.original k R B) := by
  letI : Module.FinitePresentation (Polynomial R)
      (RelativeOriginalPolynomialAlgebra318.presentation k R B) := inferInstance
  exact Module.FinitePresentation.of_equiv
    (RelativeOriginalPolynomialAlgebra318.polynomialComparison k R B).toLinearEquiv
end RelativePolynomialFinitePresentation318
