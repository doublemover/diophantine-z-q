module

public import SelectedActualAbelComplexSheetJacobian318
public import Mathlib.MeasureTheory.Measure.WithDensity

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace SelectedActualAbelExceptionalSetNull318

open SelectedActualAbelComplexSheetJacobian318

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def complexDensity (D : E → E →L[ℂ] E) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(D x).toLinearMap.det‖ ^ 2)

/-- The critical value image is truly null in these same holomorphic coordinates. The
equal-real-dimension Jacobian theorem applies without presuming the critical source is
measure zero or imposing any choice of exceptional values. -/
theorem critical_image_null
    (μ : Measure E) [IsAddHaarMeasure μ] (f : E → E) (D : E → E →L[ℂ] E) (C : Set E)
    (hderiv : ∀ x ∈ C, HasFDerivWithinAt f (D x) C x)
    (hcrit : ∀ x ∈ C, (D x).toLinearMap.det = 0) :
    μ (f '' C) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => (D x).restrictScalars ℝ)
  · intro x hx
    exact (hderiv x hx).restrictScalars ℝ
  · intro x hx
    apply abs_eq_zero.mp
    rw [abs_real_det_eq_complex_det_sq, hcrit x hx, norm_zero, zero_pow (by decide)]

/-- Any discarded source coordinate slices that have zero chart measure also have
null target image. Unlike the critical image step, this uses source nullness. -/
theorem discarded_image_null
    (μ : Measure E) [IsAddHaarMeasure μ] (f : E → E) (D : E → E →L[ℂ] E) (Q : Set E)
    (hderiv : ∀ x ∈ Q, HasFDerivWithinAt f (D x) Q x) (hQ : μ Q = 0) :
    μ (f '' Q) = 0 :=
  MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (fun x hx => ((hderiv x hx).restrictScalars ℝ).differentiableWithinAt) hQ

/-- The weighted source has zero mass on critical source points, even when the
unweighted source has not been shown null. -/
theorem weighted_critical_null
    (μ : Measure E) (D : E → E →L[ℂ] E) (C : Set E) (hC : MeasurableSet C)
    (hcrit : ∀ x ∈ C, (D x).toLinearMap.det = 0) :
    (μ.withDensity (complexDensity D)) C = 0 := by
  rw [withDensity_apply _ hC]
  apply setLIntegral_eq_zero hC
  intro x hx
  simp only [complexDensity, hcrit x hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    ENNReal.ofReal_zero, Pi.zero_apply]

/-- On a genuine injective analytic coordinate patch, the pullback of any measurable
null target is null for the same determinant-weighted source measure. No assumption
is made that all discarded ordinary source points are critical. -/
theorem weighted_preimage_null_on_injective_patch
    (μ : Measure E) [IsAddHaarMeasure μ] (f : E → E) (D : E → E →L[ℂ] E)
    (S A : Set E) (hf : Measurable f) (hS : MeasurableSet S) (hA : MeasurableSet A)
    (hnull : μ A = 0) (hderiv : ∀ x ∈ S, HasFDerivWithinAt f (D x) S x)
    (hinj : InjOn f S) :
    (μ.withDensity (complexDensity D)) (f ⁻¹' A ∩ S) = 0 := by
  have h := complex_density_sheet_pushforward μ f D S (f '' S) hS hderiv hinj rfl
  change Measure.map f ((μ.withDensity (complexDensity D)).restrict S) =
    μ.restrict (f '' S) at h
  have he := congrArg (fun m : Measure E => m A) h
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA), Measure.restrict_apply hA] at he
  exact he.trans (measure_mono_null inter_subset_left hnull)

end SelectedActualAbelExceptionalSetNull318

#print axioms SelectedActualAbelExceptionalSetNull318.critical_image_null
#print axioms SelectedActualAbelExceptionalSetNull318.weighted_critical_null
#print axioms SelectedActualAbelExceptionalSetNull318.weighted_preimage_null_on_injective_patch
