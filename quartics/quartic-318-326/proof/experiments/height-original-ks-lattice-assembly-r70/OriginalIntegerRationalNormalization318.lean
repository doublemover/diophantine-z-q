module
public import IntegralClosureSubmonoidField318
public import OriginalIntegerFiniteClosure318
public import Mathlib.RingTheory.RegularLocalRing.Defs
public section
noncomputable section
namespace OriginalIntegerRationalNormalization318
open Polynomial
open scoped TensorProduct
/-- Capture the native tensor-left algebra on a symbolic carrier before
specializing the deeply nested integral-closure subtype. -/
@[expose] def integerTensorAlgebra (A : Type*) [CommRing A] : Algebra A (A ⊗[ℤ] ℚ) :=
  inferInstance

private theorem integerTensorAlgebra_map (A : Type*) [CommRing A] :
    @algebraMap A (A ⊗[ℤ] ℚ) _ _ (integerTensorAlgebra A) =
      Algebra.TensorProduct.includeLeftRingHom := rfl

variable (c : Fin 4 → ℚˣ)
abbrev K := RatFunc ℚ
abbrev L := OriginalIntegerFiniteClosure318.L c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra
attribute [local instance] IntegerPolynomialFractionField318.fieldAlgebra
attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra

/-- The rational parameter action in the same original Kummer field. -/
@[expose] def rationalBaseAlgebra : Algebra ℚ[X] (L c) :=
  ((algebraMap K (L c)).comp (algebraMap ℚ[X] K)).toAlgebra
attribute [local instance] rationalBaseAlgebra

local instance rationalTower : @IsScalarTower ℚ[X] K (L c)
    (inferInstance : Algebra ℚ[X] K).toSMul
    (inferInstance : Algebra K (L c)).toSMul (rationalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ[X]) (S := K) (A := L c) rfl

local instance coefficientTower : @IsScalarTower ℤ[X] ℚ[X] (L c)
    OriginalIntegerAffineModel318.rationalPolynomialAlgebra.toSMul
    (rationalBaseAlgebra c).toSMul (OriginalIntegerFiniteClosure318.baseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ[X]) (S := ℚ[X]) (A := L c) rfl

/-- The normalized rational affine curve, not the unnormalized monic order. -/
abbrev RationalClosure := integralClosure ℚ[X] (L c)
abbrev IntegerClosure := OriginalIntegerFiniteClosure318.Closure c
abbrev denominators := Algebra.algebraMapSubmonoid (IntegerClosure c)
  IntegerPolynomialLocalization318.denominators

@[expose] def rationalization : IntegerClosure c →ₐ[ℤ[X]] RationalClosure c :=
  IntegralClosureLocalizationField318.inclusion ℤ[X] ℚ[X] (L c)

@[expose] def rationalizationAlgebra : Algebra (IntegerClosure c) (RationalClosure c) :=
  (rationalization c).toRingHom.toAlgebra
attribute [local instance] rationalizationAlgebra

/-- The actual normalized rational chart is obtained by inverting ONLY
nonzero integer coefficient denominators. The parameter is not inverted. -/
theorem actual_localization : IsLocalization (denominators c) (RationalClosure c) := by
  letI := IntegerPolynomialLocalization318.rational_polynomial_localization
  exact IntegralClosureSubmonoidField318.localization ℤ[X] ℚ[X] (L c)
    IntegerPolynomialLocalization318.denominators

/-- A canonical coefficient-base-change identification, preserving the
actual integer-closure inclusion. It is not an arbitrary function-field iso. -/
@[expose] def rationalFiberEquiv :
    IntegerClosure c ⊗[ℤ[X]] ℚ[X] ≃ₐ[IntegerClosure c] RationalClosure c := by
  letI := IntegerPolynomialLocalization318.rational_polynomial_localization
  letI := actual_localization c
  exact IsLocalization.algEquiv (denominators c) _ _

/-- The polynomial-base denominator set is exactly the image of the
nonzero integers. No parameter or contact polynomial is silently inverted. -/
theorem denominators_eq_integer : denominators c =
    Algebra.algebraMapSubmonoid (IntegerClosure c) (nonZeroDivisors ℤ) := by
  ext z
  constructor
  · rintro ⟨p, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, IsScalarTower.algebraMap_apply ℤ ℤ[X] (IntegerClosure c) n⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨algebraMap ℤ ℤ[X] n, ⟨n, hn, rfl⟩,
      (IsScalarTower.algebraMap_apply ℤ ℤ[X] (IntegerClosure c) n).symm⟩

/-- The actual affine rational fiber over Spec Z, with the integer-closure
map retained, is the literal rational-parameter integral closure in L. -/
@[expose] def integerRationalFiberEquiv :
    letI : Algebra (IntegerClosure c) (IntegerClosure c ⊗[ℤ] ℚ) :=
      integerTensorAlgebra (IntegerClosure c)
    IntegerClosure c ⊗[ℤ] ℚ ≃ₐ[IntegerClosure c] RationalClosure c := by
  letI : Algebra (IntegerClosure c) (IntegerClosure c ⊗[ℤ] ℚ) :=
    integerTensorAlgebra (IntegerClosure c)
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (IntegerClosure c) (nonZeroDivisors ℤ))
      (RationalClosure c) := by
    rw [← denominators_eq_integer c]
    exact actual_localization c
  exact IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (IntegerClosure c) (nonZeroDivisors ℤ))
    (IntegerClosure c ⊗[ℤ] ℚ) (RationalClosure c)

/-- In characteristic zero the normalized affine rational chart is Dedekind:
Q[T], unlike Z[T], is a PID, and the original Kummer extension is finite
separable. This does not imply regularity of arithmetic special fibers. -/
theorem rational_dedekind : IsDedekindDomain (RationalClosure c) := by
  letI : Module.Finite K (L c) := OriginalIntegerFiniteClosure318.extension_finite c
  exact integralClosure.isDedekindDomain ℚ[X] K (L c)

theorem rational_regular : IsRegularRing (RationalClosure c) := by
  letI := rational_dedekind c
  infer_instance

theorem rational_stalk_regular (p : Ideal (RationalClosure c)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  letI := rational_regular c
  exact IsRegularRing.isRegularLocalRing_localization (R := RationalClosure c) p

/-- Regularity of the actual rational base-change ring, not of the integral
model at bad primes. This includes every prime of the whole affine fiber. -/
theorem integerRationalFiber_regular : IsRegularRing (IntegerClosure c ⊗[ℤ] ℚ) := by
  letI : Algebra (IntegerClosure c) (IntegerClosure c ⊗[ℤ] ℚ) :=
    integerTensorAlgebra (IntegerClosure c)
  letI := rational_regular c
  exact IsRegularRing.of_ringEquiv (R := RationalClosure c)
    (R' := IntegerClosure c ⊗[ℤ] ℚ) (integerRationalFiberEquiv c).toRingEquiv.symm

end OriginalIntegerRationalNormalization318
