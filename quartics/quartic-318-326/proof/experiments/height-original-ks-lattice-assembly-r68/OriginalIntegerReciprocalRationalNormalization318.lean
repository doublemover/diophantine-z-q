module
public import OriginalIntegerRationalNormalization318
public import OriginalIntegerReciprocalFiniteClosure318
public section
noncomputable section
namespace OriginalIntegerReciprocalRationalNormalization318
open Polynomial
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
abbrev R := Polynomial ℤ
abbrev K := RatFunc ℚ
abbrev L := OriginalIntegerReciprocalOrderField318.L c
abbrev Order := OriginalIntegerReciprocalOrderField318.Order c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra
attribute [local instance] IntegerPolynomialFractionField318.fieldAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
attribute [local instance] OriginalIntegerReciprocalOrderField318.fieldAlgebra
local instance parameterFraction : IsFractionRing R K :=
  IntegerPolynomialFractionField318.actual_fractionField

/-- Extend the actual RECIPROCAL parameter map, not the finite parameter
map, to its rational function field. The ambient original L is unchanged. -/
@[expose] def rationalFunctionAlgebra : Algebra K (L c) :=
  (IsFractionRing.lift (OriginalIntegerReciprocalFiniteClosure318.coefficient_injective c) :
    K →+* L c).toAlgebra
attribute [local instance] rationalFunctionAlgebra

local instance coefficientFieldTower : @IsScalarTower R K (L c)
    IntegerPolynomialFractionField318.fieldAlgebra.toSMul
    (rationalFunctionAlgebra c).toSMul
    (OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := K) (A := L c)
    (fun p => (IsFractionRing.lift_algebraMap
      (OriginalIntegerReciprocalFiniteClosure318.coefficient_injective c) p).symm)

@[expose] def rationalBaseAlgebra : Algebra ℚ[X] (L c) :=
  ((algebraMap K (L c)).comp (algebraMap ℚ[X] K)).toAlgebra
attribute [local instance] rationalBaseAlgebra

local instance rationalTower : @IsScalarTower ℚ[X] K (L c)
    (inferInstance : Algebra ℚ[X] K).toSMul
    (rationalFunctionAlgebra c).toSMul (rationalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ[X]) (S := K) (A := L c) rfl

local instance coefficientTower : @IsScalarTower R ℚ[X] (L c)
    OriginalIntegerAffineModel318.rationalPolynomialAlgebra.toSMul
    (rationalBaseAlgebra c).toSMul
    (OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := ℚ[X]) (A := L c)
    (fun p => (IsFractionRing.lift_algebraMap
      (OriginalIntegerReciprocalFiniteClosure318.coefficient_injective c) p).symm)

/-- Finiteness for this precise rational-function action follows from the
actual reciprocal order/fraction field, not equality with the finite action. -/
theorem extension_finite : Module.Finite K (L c) := by
  letI := OriginalIntegerReciprocalOrderField318.order_domain c
  letI := OriginalIntegerReciprocalOrderField318.field_scalar_tower c
  letI := OriginalIntegerReciprocalOrderField318.actual_fractionField c
  letI : Module.Finite R (Order c) :=
    (OriginalIntegerReciprocalCharts318.reciprocal_finite_free c).1
  exact FiniteOrderFractionExtension318.finite R (Order c) K (L c)
    (OriginalIntegerReciprocalFiniteClosure318.coefficient_injective c)

abbrev IntegerClosure := OriginalIntegerReciprocalNormalization318.Closure c
abbrev RationalClosure := integralClosure ℚ[X] (L c)
abbrev denominators := Algebra.algebraMapSubmonoid (IntegerClosure c)
  IntegerPolynomialLocalization318.denominators

@[expose] def rationalization : IntegerClosure c →ₐ[R] RationalClosure c :=
  IntegralClosureLocalizationField318.inclusion R ℚ[X] (L c)
@[expose] def rationalizationAlgebra : Algebra (IntegerClosure c) (RationalClosure c) :=
  (rationalization c).toRingHom.toAlgebra
attribute [local instance] rationalizationAlgebra

theorem actual_localization : IsLocalization (denominators c) (RationalClosure c) := by
  letI := IntegerPolynomialLocalization318.rational_polynomial_localization
  exact IntegralClosureSubmonoidField318.localization R ℚ[X] (L c)
    IntegerPolynomialLocalization318.denominators

theorem denominators_eq_integer : denominators c =
    Algebra.algebraMapSubmonoid (IntegerClosure c) (nonZeroDivisors ℤ) := by
  ext z
  constructor
  · rintro ⟨p, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, IsScalarTower.algebraMap_apply ℤ R (IntegerClosure c) n⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨algebraMap ℤ R n, ⟨n, hn, rfl⟩,
      (IsScalarTower.algebraMap_apply ℤ R (IntegerClosure c) n).symm⟩

/-- The WHOLE reciprocal rational affine fiber, not just an overlap or a
localization at a branch parameter. Only integer denominators are inverted. -/
@[expose] def integerRationalFiberEquiv :
    IntegerClosure c ⊗[ℤ] ℚ ≃ₐ[IntegerClosure c] RationalClosure c := by
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (IntegerClosure c) (nonZeroDivisors ℤ))
      (RationalClosure c) := by
    rw [← denominators_eq_integer c]
    exact actual_localization c
  exact IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (IntegerClosure c) (nonZeroDivisors ℤ)) _ _

theorem rational_dedekind : IsDedekindDomain (RationalClosure c) := by
  letI := extension_finite c
  exact integralClosure.isDedekindDomain ℚ[X] K (L c)

theorem integerRationalFiber_regular : IsRegularRing (IntegerClosure c ⊗[ℤ] ℚ) := by
  letI := rational_dedekind c
  exact IsRegularRing.of_ringEquiv (integerRationalFiberEquiv c).toRingEquiv.symm

theorem integerRationalFiber_stalk_regular
    (p : Ideal (IntegerClosure c ⊗[ℤ] ℚ)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  letI := integerRationalFiber_regular c
  infer_instance

end OriginalIntegerReciprocalRationalNormalization318
