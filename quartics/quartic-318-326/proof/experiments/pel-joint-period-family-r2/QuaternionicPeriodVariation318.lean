module
public import QuaternionicHodgeKernel318
public import Mathlib.Analysis.Calculus.Deriv.Basic
public section
noncomputable section
namespace QuaternionicPeriodVariation318
open QuaternionicHodgeKernel318
set_option maxHeartbeats 600000

/-- Differentiate the ACTUAL kernel inclusion as τ varies in the upper half
plane: each row (z,-zτ) has derivative (0,-z). -/
@[expose] def variation : Vectors →ₗ[ℂ] Matrices where
  toFun z i := ![0,-z i]
  map_add' z w := by funext i j; fin_cases j <;> simp
  map_smul' a z := by funext i j; fin_cases j <;> simp

theorem inclusion_derivative (τ : ℂ) (z : Vectors) (i j : Fin 2) :
    HasDerivAt (fun w : ℂ => inclusion w z i j) (variation z i j) τ := by
  fin_cases j
  · change HasDerivAt (fun _ : ℂ => z i) 0 τ
    exact hasDerivAt_const τ (z i)
  · change HasDerivAt (fun w : ℂ => -z i*w) (-z i) τ
    simpa only [mul_one] using (hasDerivAt_id τ).const_mul (-z i)

theorem variation_projection (τ : ℂ) (z : Vectors) :
    projection τ (variation z)=-z := by
  funext i
  simp only [projection,variation,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.cons_val_zero,Matrix.cons_val_one,zero_mul,zero_add,Pi.neg_apply]

/-- The second fundamental map of this precise period-kernel family. This
is linear analytic variation, not yet an algebraic or metrized KS theorem. -/
@[expose] def secondFundamental (τ : ℂ) : Hodge τ →ₗ[ℂ] Vectors :=
  (projection τ).comp (variation.comp (frame τ).symm.toLinearMap)

theorem secondFundamental_frame (τ : ℂ) (z : Vectors) :
    secondFundamental τ (frame τ z)=-z := by
  change projection τ (variation ((frame τ).symm (frame τ z)))=-z
  rw [LinearEquiv.symm_apply_apply,variation_projection]

theorem secondFundamental_bijective (τ : ℂ) : Function.Bijective (secondFundamental τ) := by
  constructor
  · intro M N h
    apply (frame τ).symm.injective
    have hh : -((frame τ).symm M) = -((frame τ).symm N) := by
      change projection τ (variation ((frame τ).symm M))=
        projection τ (variation ((frame τ).symm N)) at h
      simpa only [variation_projection] using h
    exact neg_injective hh
  · intro z
    refine ⟨frame τ (-z),?_⟩
    rw [secondFundamental_frame,neg_neg]
end QuaternionicPeriodVariation318
