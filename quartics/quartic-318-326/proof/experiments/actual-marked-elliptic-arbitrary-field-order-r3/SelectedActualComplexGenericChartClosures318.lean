module
public import SelectedActualComplexReciprocalRatFunc318
public import JLineOverlap318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
namespace SelectedActualComplexGenericChartClosures318

abbrev JField := RatFunc ℂ

/-- The reciprocal map with the literal RatFunc coefficient algebra.
The competing division-ring ℂ action is not installed in the term. -/
@[expose] def reciprocalPolynomial : ℂ[X] →+* JField := by
  letI : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  exact (Polynomial.aeval ((RatFunc.X : JField)⁻¹)).toRingHom

/-- Base chart 1 is J; chart 0 is J⁻¹, in the same C(J). -/
@[expose] def basePolynomial (i : Fin 2) : ℂ[X] →+* JField :=
  if i = 0 then reciprocalPolynomial else algebraMap ℂ[X] JField

theorem basePolynomial_C (i : Fin 2) (r : ℂ) :
    basePolynomial i (C r) = algebraMap ℂ JField r := by
  by_cases hi : i = 0
  · rw [basePolynomial, if_pos hi]
    letI : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
    change Polynomial.aeval ((RatFunc.X : JField)⁻¹) (C r) = _
    exact Polynomial.aeval_C _ _
  · rw [basePolynomial, if_neg hi]
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

theorem basePolynomial_X₀ : basePolynomial 0 X = (RatFunc.X : JField)⁻¹ := by
  rw [basePolynomial,if_pos rfl]
  letI : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  change aeval ((RatFunc.X : JField)⁻¹) (X : ℂ[X]) = _
  exact Polynomial.aeval_X _

theorem basePolynomial_X₁ : basePolynomial 1 X = (RatFunc.X : JField) := by
  simp [basePolynomial,RatFunc.algebraMap_X]

/-- Each chart's fraction field is literally the same field C(J),
with the correct (possibly reciprocal) polynomial action. -/
theorem base_fractionRing (i : Fin 2) :
    letI : Algebra ℂ[X] JField := (basePolynomial i).toAlgebra
    IsFractionRing ℂ[X] JField := by
  fin_cases i
  · change (letI : Algebra ℂ[X] JField := (basePolynomial (0:Fin 2)).toAlgebra
            IsFractionRing ℂ[X] JField)
    have h₀ : basePolynomial (0:Fin 2) = reciprocalPolynomial := if_pos rfl
    rw [h₀]
    letI : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
    change (letI : Algebra ℂ[X] JField :=
              (Polynomial.aeval ((RatFunc.X : JField)⁻¹)).toRingHom.toAlgebra
            IsFractionRing ℂ[X] JField)
    exact SelectedActualComplexReciprocalRatFunc318.inverse_fractionRing
  · change (letI : Algebra ℂ[X] JField := (basePolynomial (1:Fin 2)).toAlgebra
            IsFractionRing ℂ[X] JField)
    have h₁ : basePolynomial (1:Fin 2) = algebraMap ℂ[X] JField := by simp [basePolynomial]
    rw [h₁,toAlgebra_algebraMap]
    infer_instance

variable (K : Type) [Field K] [Algebra JField K]

/-- Both affine orders are subrings of this SAME entire field K.
Only the polynomial embedding changes across the projective cover. -/
@[expose] def polynomial (i : Fin 2) : ℂ[X] →+* K :=
  (algebraMap JField K).comp (basePolynomial i)

@[expose] def coordinate : K := algebraMap JField K (RatFunc.X : JField)

theorem coordinate_ne_zero : coordinate K ≠ 0 := by
  intro h
  apply RatFunc.X_ne_zero (K := ℂ)
  apply (algebraMap JField K).injective
  exact h.trans (map_zero (algebraMap JField K)).symm

theorem polynomial_X₀ : polynomial K 0 X = (coordinate K)⁻¹ := by
  simp only [polynomial,RingHom.comp_apply,basePolynomial_X₀,map_inv₀,coordinate]

theorem polynomial_X₁ : polynomial K 1 X = coordinate K := by
  rw [polynomial,RingHom.comp_apply,basePolynomial_X₁,coordinate]

/-- The actual relative field point of the original projective J-line.
This is a morphism into the original standard chart, not a glued
replacement projective curve. -/
@[expose] def genericMap : Spec (CommRingCat.of K) ⟶ ProjectiveJLine318.scheme ℂ :=
  Spec.map (CommRingCat.ofHom (polynomial K 1)) ≫ JLineAtlas318.chart ℂ 1

variable [aK : Algebra ℂ K] [hTower : IsScalarTower ℂ JField K]

include hTower in
theorem polynomial_eq_aeval (i : Fin 2) :
    polynomial K i = (Polynomial.aeval (polynomial K i X)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change algebraMap JField K (basePolynomial i (C r)) =
      aeval (polynomial K i X) (C r)
    rw [basePolynomial_C,aeval_C,← IsScalarTower.algebraMap_apply ℂ JField K]
  · exact (Polynomial.aeval_X _).symm

include aK hTower in
/-- The two generic expressions agree in the genuine projective overlap.
The reciprocal chart evaluation is not an independent field point. -/
theorem genericMap_factor (i : Fin 2) :
    genericMap K = Spec.map (CommRingCat.ofHom (polynomial K i)) ≫ JLineAtlas318.chart ℂ i := by
  fin_cases i
  · change genericMap K =
      Spec.map (CommRingCat.ofHom (polynomial K (0:Fin 2))) ≫ JLineAtlas318.chart ℂ (0:Fin 2)
    let u := Units.mk0 (coordinate K) (coordinate_ne_zero K)
    have h := JLineOverlap318.unit_chart_overlap (R := ℂ) u
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
    letI : Algebra ℂ[X] K := (polynomial K i).toAlgebra
    Module.Finite ℂ[X] (integralClosure ℂ[X] K) :=
  polynomial_order_finite (T:=K) (basePolynomial i) (base_fractionRing i)

/-- Normality is for the same concrete integral closure, in K itself. -/
theorem closure_normal (i : Fin 2) :
    letI : Algebra ℂ[X] K := (polynomial K i).toAlgebra
    IsIntegrallyClosed (integralClosure ℂ[X] K) := by
  letI : Algebra ℂ[X] K := (polynomial K i).toAlgebra
  letI : IsIntegrallyClosedIn (integralClosure ℂ[X] K) K :=
    IsIntegrallyClosedIn.of_isIntegralClosure (R := ℂ[X])
  letI : FaithfulSMul (integralClosure ℂ[X] K) K :=
    IsIntegralClosure.faithfulSMul ℂ[X] (integralClosure ℂ[X] K) K
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure ℂ[X] K) K

end SelectedActualComplexGenericChartClosures318

#print axioms SelectedActualComplexGenericChartClosures318.genericMap_factor
#print axioms SelectedActualComplexGenericChartClosures318.closure_finite
#print axioms SelectedActualComplexGenericChartClosures318.closure_normal
