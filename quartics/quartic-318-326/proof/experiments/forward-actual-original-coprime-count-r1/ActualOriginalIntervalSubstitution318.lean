module
public import ActualOriginalNormalJacobian318
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public section
noncomputable section
namespace ActualOriginalIntervalSubstitution318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalJointLevelDensity318
open ActualOriginalNormalJacobian318
set_option maxHeartbeats 16000000

/-- Genuine original one-coordinate change of variables on every positive
a interval. The continuous phase is arbitrary, so the statement applies
to the exact complex Fourier phase without changing the Jacobian. -/
theorem original_positive_interval_substitution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ) (hW : Continuous W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0)
    (phase : ℝ→E) (hphase : Continuous phase) (v : Parameters)
    (A B : ℝ) (hA : 0<A) (hAB : A≤B) :
    (∫a in A..B,W (assemble a v) • phase (equation κ (assemble a v)))=
      ∫s in equation κ (assemble A v)..equation κ (assemble B v),
        levelDensity κ W (s,v) • phase s := by
  let f : ℝ→ℝ := fun a => equation κ (assemble a v)
  let g : ℝ→E := fun s => levelDensity κ W (s,v) • phase s
  have hf : ∀a∈Set.uIcc A B,HasDerivAt f (2*a) a :=
    fun a _ => original_normal_derivative κ a v
  have hg : Continuous g :=
    ((level_density_continuous κ η hη W hW hb).comp (continuous_id.prodMk continuous_const)).smul hphase
  have hsub := intervalIntegral.integral_deriv_smul_comp hf
    (show ContinuousOn (fun a : ℝ => 2*a) (Set.uIcc A B) by fun_prop) hg
  calc
    _ = ∫a in A..B,(2*a) • (g (f a)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      have hh : a∈Set.Icc A B := by simpa only [Set.uIcc_of_le hAB] using ha
      exact (original_phase_jacobian κ a (lt_of_lt_of_le hA hh.1) W v phase).symm
    _ = _ := hsub

end ActualOriginalIntervalSubstitution318
