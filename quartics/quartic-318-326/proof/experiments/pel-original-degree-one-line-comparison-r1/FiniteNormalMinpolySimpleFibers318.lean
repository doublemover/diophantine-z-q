module
public import WholeFiniteFractionExtension318
public import WholePolynomialSimpleFiberDensity318
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.Separable
public section
noncomputable section
namespace FiniteNormalMinpolySimpleFibers318
open Polynomial
variable (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
  [FaithfulSMul R A] [Module.Finite R A]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Every actual integral element has generically separable WHOLE
minimal polynomial over a characteristic-zero normal base. The exact
field-fraction identity is used; no special-fiber squarefreeness is
inferred merely from the original domain being reduced. -/
theorem generic_separable (t : A) :
    ((minpoly R t).map (algebraMap R (FractionRing R))).Separable := by
  let K := FractionRing R
  let L := FractionRing A
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : Module.Finite K L := WholeFiniteFractionExtension318.finite R A
  rw [←minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.of_finite R t)]
  exact (minpoly.irreducible (IsIntegral.of_finite K (algebraMap A L t))).separable
end FiniteNormalMinpolySimpleFibers318
