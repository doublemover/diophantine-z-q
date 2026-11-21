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
  · change (letI : Algebra ℚ[X] JField := (basePolynomial (0:Fin 2)).toAlgebra
            IsFractionRing ℚ[X] JField)
    have h₀ : basePolynomial (0:Fin 2) =
        (Polynomial.aeval ((RatFunc.X : JField)⁻¹)).toRingHom := by simp [basePolynomial]
    rw [h₀]
    exact ReciprocalRatFunc318.inverse_fractionRing
  · change (letI : Algebra ℚ[X] JField := (basePolynomial (1:Fin 2)).toAlgebra
            IsFractionRing ℚ[X] JField)
    have h₁ : basePolynomial (1:Fin 2) = algebraMap ℚ[X] JField := by simp [basePolynomial]
    rw [h₁,toAlgebra_algebraMap]
    infer_instance

variable (K : Type) [Field K] [Algebra JField K]

/-- Both affine orders are subrings of this SAME entire field K.
Only the polynomial embedding changes across the projective cover. -/
@[expose] def polynomial (i : Fin 2) : ℚ[X] →+* K :=
  (algebraMap JField K).comp (basePolynomial i)

@[expose] def coordinate : K := algebraMap JField K (RatFunc.X : JField)

theorem coordinate_ne_zero : coordinate K ≠ 0 := by
  intro h
  apply RatFunc.X_ne_zero
  apply (algebraMap JField K).injective
  simpa only [coordinate,map_zero] using h

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

include aK hTower in
/-- The two generic expressions agree in the genuine projective overlap.
The reciprocal chart evaluation is not an independent field point. -/
theorem genericMap_factor (i : Fin 2) :
    genericMap K = Spec.map (CommRingCat.ofHom (polynomial K i)) ≫ JLineAtlas318.chart ℚ i := by
  fin_cases i
  · change genericMap K =
      Spec.map (CommRingCat.ofHom (polynomial K (0:Fin 2))) ≫ JLineAtlas318.chart ℚ (0:Fin 2)
    let u := Units.mk0 (coordinate K) (coordinate_ne_zero K)
    have h := JLineOverlap318.unit_chart_overlap (R := ℚ) u
    rw [genericMap,polynomial_eq_aeval K 1,polynomial_eq_aeval K 0,
      polynomial_X₀,polynomial_X₁]
    simpa only [u,Units.val_mk0,Units.val_inv_eq_inv_val] using h
  · rfl

variable [hfin : FiniteDimensional JField K] [hsep : Algebra.IsSeparable JField K]

private theorem polynomial_order_finite {A E T : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [Field E] [Field T] [Algebra E T] [FiniteDimensional E T] [Algebra.IsSeparable E T]
    (c : A→+*E)
    (hc : letI : Algebra A E := c.toAlgebra; IsFractionRing A E) :
    letI : Algebra A T := ((algebraMap E T).comp c).toAlgebra
    Module.Finite A (integralClosure A T) := by
  letI : Algebra A E := c.toAlgebra
  letI : Algebra A T := ((algebraMap E T).comp c).toAlgebra
  letI : IsScalarTower A E T := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI : IsFractionRing A E := hc
  exact IsIntegralClosure.finite A E T (integralClosure A T)

include hfin hsep in
/-- Actual trace-dual finiteness on both original polynomial charts,
rather than a finite-normalization hypothesis. -/
theorem closure_finite (i : Fin 2) :
    letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
    Module.Finite ℚ[X] (integralClosure ℚ[X] K) :=
  polynomial_order_finite (T:=K) (basePolynomial i) (base_fractionRing i)

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
