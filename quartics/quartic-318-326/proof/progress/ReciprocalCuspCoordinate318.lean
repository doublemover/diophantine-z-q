module
public import ActualJCusp318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public section
noncomputable section
open Filter Topology ActualJCusp318
namespace ReciprocalCuspCoordinate318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

lemma derivative_ne_zero : deriv reciprocalGerm 0 ≠ 0 := by
  rw [reciprocalGerm_hasDerivAt.deriv]
  exact one_ne_zero

/-- The actual analytic inverse function for the filled reciprocal-j germ. -/
@[expose] def inverseGerm : ℂ → ℂ :=
  reciprocalGerm_analytic.hasStrictDerivAt.localInverse _ _ _ derivative_ne_zero

theorem inverseGerm_analytic : AnalyticAt ℂ inverseGerm 0 := by
  simpa only [inverseGerm,reciprocalGerm_zero] using!
    reciprocalGerm_analytic.analyticAt_localInverse derivative_ne_zero

theorem inverseGerm_zero : inverseGerm 0=0 := by
  have h := HasStrictFDerivAt.localInverse_apply_image
    (reciprocalGerm_analytic.hasStrictDerivAt.hasStrictFDerivAt_equiv derivative_ne_zero)
  simpa only [inverseGerm,reciprocalGerm_zero] using! h

theorem inverseGerm_left : ∀ᶠq in 𝓝 (0:ℂ), inverseGerm (reciprocalGerm q)=q :=
  HasStrictDerivAt.eventually_left_inverse
    (hf:=reciprocalGerm_analytic.hasStrictDerivAt) (hf':=derivative_ne_zero)

theorem inverseGerm_right : ∀ᶠs in 𝓝 (0:ℂ), reciprocalGerm (inverseGerm s)=s := by
  simpa only [inverseGerm,reciprocalGerm_zero] using!
    (HasStrictDerivAt.eventually_right_inverse
      (hf:=reciprocalGerm_analytic.hasStrictDerivAt) (hf':=derivative_ne_zero))

theorem inverseGerm_hasDerivAt : HasDerivAt inverseGerm 1 0 := by
  have h := (reciprocalGerm_analytic.hasStrictDerivAt.to_localInverse derivative_ne_zero).hasDerivAt
  simpa only [inverseGerm,reciprocalGerm_zero,reciprocalGerm_hasDerivAt.deriv,inv_one] using! h

/-- Exact recovery of the original q-parameter from reciprocal j sufficiently
far up the genuine cusp. No global compactification is assumed. -/
theorem recover_q_eventually : ∀ᶠtau:UpperHalfPlane in UpperHalfPlane.atImInfty,
    inverseGerm ((ActualQJ318.jInvariant tau)⁻¹)=Function.Periodic.qParam 1 tau := by
  have h := (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).eventually
    inverseGerm_left
  simpa only [ActualJCusp318.reciprocalGerm_qParam] using h

/-- The inverse-function theorem supplies a genuine local coordinate
homeomorphism, not merely a formal inverse-power-series name. -/
@[expose] def coordinate : OpenPartialHomeomorph ℂ ℂ :=
  (reciprocalGerm_analytic.hasStrictDerivAt.hasStrictFDerivAt_equiv derivative_ne_zero).toOpenPartialHomeomorph reciprocalGerm

theorem coordinate_coe : (coordinate : ℂ → ℂ)=reciprocalGerm := rfl

theorem coordinate_zero_source : (0:ℂ)∈coordinate.source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

theorem coordinate_zero_target : (0:ℂ)∈coordinate.target := by
  simpa only [coordinate_coe,reciprocalGerm_zero] using
    coordinate.map_source coordinate_zero_source

theorem coordinate_inverse : (coordinate.symm : ℂ → ℂ)=inverseGerm := rfl

end ReciprocalCuspCoordinate318
