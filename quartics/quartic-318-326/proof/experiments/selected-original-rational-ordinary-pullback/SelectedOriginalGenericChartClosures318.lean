module
public import ReciprocalRatFunc318
public import JLineOverlap318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
namespace SelectedOriginalGenericChartClosures318

abbrev JField := RatFunc ℚ

/-- Base chart 1 is J; chart 0 is J⁻¹, in the same Q(J). -/
@[expose] def basePolynomial (i : Fin 2) : ℚ[X] →+* JField :=
  if i = 0 then (Polynomial.aeval ((RatFunc.X : JField)⁻¹)).toRingHom
  else algebraMap ℚ[X] JField

theorem basePolynomial_C (i : Fin 2) (r : ℚ) :
    basePolynomial i (C r) = algebraMap ℚ JField r := by
  fin_cases i <;>
    simp [basePolynomial,Polynomial.aeval_C,RatFunc.algebraMap_C,← RatFunc.algebraMap_eq_C]

theorem basePolynomial_X₀ : basePolynomial 0 X = (RatFunc.X : JField)⁻¹ := by
  simp [basePolynomial]

theorem basePolynomial_X₁ : basePolynomial 1 X = (RatFunc.X : JField) := by
  simp [basePolynomial,RatFunc.algebraMap_X]

/-- Each chart's fraction field is literally the same field Q(J),
with the correct (possibly reciprocal) polynomial action. -/
theorem base_fractionRing (i : Fin 2) :
    letI : Algebra ℚ[X] JField := (basePolynomial i).toAlgebra
    IsFractionRing ℚ[X] JField := by
  fin_cases i
  · simpa [basePolynomial] using ReciprocalRatFunc318.inverse_fractionRing
  · simpa [basePolynomial,toAlgebra_algebraMap] using
      (inferInstance : IsFractionRing ℚ[X] JField)

variable (K : Type) [Field K] [Algebra JField K]

/-- Both affine orders are subrings of this SAME entire field K.
Only the polynomial embedding changes across the projective cover. -/
@[expose] def polynomial (i : Fin 2) : ℚ[X] →+* K :=
  (algebraMap JField K).comp (basePolynomial i)

@[expose] def coordinate : K := algebraMap JField K (RatFunc.X : JField)

theorem coordinate_ne_zero : coordinate K ≠ 0 :=
  (algebraMap JField K).injective.ne RatFunc.X_ne_zero

theorem polynomial_X₀ : polynomial K 0 X = (coordinate K)⁻¹ := by
  simp only [polynomial,RingHom.comp_apply,basePolynomial_X₀,map_inv₀,coordinate]

theorem polynomial_X₁ : polynomial K 1 X = coordinate K := by
  rw [polynomial,RingHom.comp_apply,basePolynomial_X₁,coordinate]

/-- The actual relative field point of the original projective J-line.
This is a morphism into the original standard chart, not a glued
replacement projective curve. -/
@[expose] def genericMap : Spec (CommRingCat.of K) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.map (CommRingCat.ofHom (polynomial K 1)) ≫ JLineAtlas318.chart ℚ 1

variable [aK : Algebra ℚ K] [hTower : IsScalarTower ℚ JField K]

include hTower in
theorem polynomial_eq_aeval (i : Fin 2) :
    polynomial K i = (Polynomial.aeval (polynomial K i X)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change algebraMap JField K (basePolynomial i (C r)) =
      aeval (polynomial K i X) (C r)
    rw [basePolynomial_C,aeval_C,← IsScalarTower.algebraMap_apply ℚ JField K]
  · exact (Polynomial.aeval_X _).symm

/-- The two generic expressions agree in the genuine projective overlap.
The reciprocal chart evaluation is not an independent field point. -/
include aK hTower in
theorem genericMap_factor (i : Fin 2) :
    genericMap K = Spec.map (CommRingCat.ofHom (polynomial K i)) ≫ JLineAtlas318.chart ℚ i := by
  fin_cases i
  · let u := Units.mk0 (coordinate K) (coordinate_ne_zero K)
    have h := JLineOverlap318.unit_chart_overlap (R := ℚ) u
    rw [genericMap,polynomial_eq_aeval K 1,polynomial_eq_aeval K 0,
      polynomial_X₀,polynomial_X₁]
    simpa only [u,Units.val_mk0,Units.val_inv_eq_inv_val] using h
  · rfl

variable [hfin : FiniteDimensional JField K] [hsep : Algebra.IsSeparable JField K]

/-- Actual trace-dual finiteness on both original polynomial charts,
rather than a finite-normalization hypothesis. -/
include hfin hsep in
theorem closure_finite (i : Fin 2) :
    letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
    Module.Finite ℚ[X] (integralClosure ℚ[X] K) := by
  letI : Algebra ℚ[X] JField := (basePolynomial i).toAlgebra
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  letI : IsScalarTower ℚ[X] JField K :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsFractionRing ℚ[X] JField := base_fractionRing i
  exact IsIntegralClosure.finite ℚ[X] JField K (integralClosure ℚ[X] K)

/-- Normality is for the same concrete integral closure, in K itself. -/
theorem closure_normal (i : Fin 2) :
    letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
    IsIntegrallyClosed (integralClosure ℚ[X] K) := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  letI : IsIntegrallyClosedIn (integralClosure ℚ[X] K) K :=
    IsIntegrallyClosedIn.of_isIntegralClosure (R := ℚ[X])
  letI : FaithfulSMul (integralClosure ℚ[X] K) K :=
    IsIntegralClosure.faithfulSMul ℚ[X] (integralClosure ℚ[X] K) K
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure ℚ[X] K) K

end SelectedOriginalGenericChartClosures318

#print axioms SelectedOriginalGenericChartClosures318.genericMap_factor
#print axioms SelectedOriginalGenericChartClosures318.closure_finite
#print axioms SelectedOriginalGenericChartClosures318.closure_normal
