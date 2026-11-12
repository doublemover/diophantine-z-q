module
public import ActualOriginalNormalFourierDecay318
public section
noncomputable section
namespace ActualOriginalUndampedIntegrability318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318
open ActualOriginalNormalLevelChart318 ActualOriginalJointLevelDensity318
open ActualOriginalSmoothLevelDensity318 ActualOriginalNormalFourierDecay318
open ActualOriginalAmbientNormalIntegral318 ActualOriginalAmbientFourierIdentity318
open ActualOriginalNormalProfile318 MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- The complexification of the EXACT original compact smooth density.
The real-to-complex map changes no source coordinate, measure or weight. -/
@[expose] def complexLevelSchwartz (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) :
    SchwartzMap LevelParameters ℂ := by
  have hc : HasCompactSupport (fun z => (levelDensity κ W z : ℂ)) := by
    apply (level_density_compact κ η hη W hWc hb).mono
    intro z hz hzero
    apply hz
    simp only [hzero,Complex.ofReal_zero]
  exact hc.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (actual_level_density_smooth κ η hη W hW hb))

lemma complexLevelSchwartz_apply (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0)
    (z : LevelParameters) :
    complexLevelSchwartz κ η hη W hW hWc hb z = (levelDensity κ W z : ℂ) := rfl

/-- Fubini identifies the directional Fourier integral of the produced
joint Schwartz density with the SAME original five-coordinate oscillation.
The integrability needed by Fubini is produced before it is invoked. -/
theorem actual_original_joint_fourier (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) (t : ℝ) :
    originalOscillation κ W t =
      normalFourier (complexLevelSchwartz κ η hη W hW hWc hb) t := by
  let F : LevelParameters → ℂ := fun z => levelDensity κ W z • originalPhase t z.1
  have hFc : HasCompactSupport F := by
    apply (level_density_compact κ η hη W hWc hb).mono
    intro z hz hzero
    apply hz
    simp only [F,hzero,zero_smul]
  have hFcont : Continuous F :=
    (level_density_continuous κ η hη W hW.continuous hb).smul
      ((originalPhase_continuous t).comp continuous_fst)
  have hFi : Integrable F := hFcont.integrable_of_hasCompactSupport hFc
  calc
    originalOscillation κ W t = ∫ s : ℝ, normalProfile κ W s • originalPhase t s :=
      actual_original_ambient_normal_integral κ η hη W hW.continuous hWc hb
        (originalPhase t) (originalPhase_continuous t)
    _ = ∫ s : ℝ, ∫ v : Parameters, F (s,v) := by
      apply integral_congr_ae
      filter_upwards with s
      exact (integral_smul_const (fun v : Parameters => levelDensity κ W (s,v))
        (originalPhase t s)).symm
    _ = ∫ z : LevelParameters, F z := (integral_prod F hFi).symm
    _ = normalFourier (complexLevelSchwartz κ η hη W hW hWc hb) t := by
      rw [normalFourier,Real.vector_fourierIntegral_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with z
      change levelDensity κ W z • originalPhase t z.1 =
        Complex.exp (↑(-2 * Real.pi * (z.1*t)) * Complex.I) • (levelDensity κ W z : ℂ)
      rw [real_smul_original_phase]
      simp only [originalPhase,mul_assoc]

/-- Genuine absolute integrability of the original UNREGULARIZED
oscillatory integral over all real frequencies. -/
theorem actual_original_oscillation_integrable (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) :
    Integrable (originalOscillation κ W) := by
  have he : originalOscillation κ W =
      normalFourier (complexLevelSchwartz κ η hη W hW hWc hb) := by
    funext t
    exact actual_original_joint_fourier κ η hη W hW hWc hb t
  rw [he]
  exact normalFourier_integrable _

/-- The same actual original oscillation has every produced polynomial
decay bound, in particular the quadratic bound needed for absolute
one-dimensional frequency integrability. -/
theorem actual_original_oscillation_power_bound (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖t‖^n * ‖originalOscillation κ W t‖ ≤ C := by
  obtain ⟨C,hC⟩ := normalFourier_power_bound
    (complexLevelSchwartz κ η hη W hW hWc hb) n
  refine ⟨C,fun t => ?_⟩
  rw [actual_original_joint_fourier κ η hη W hW hWc hb]
  exact hC t

end ActualOriginalUndampedIntegrability318
