module
public import ActualOriginalUndampedIntegrability318
public section
noncomputable section
namespace ActualOriginalUndampedSingularIntegral318
open QuadricCRTAssembly318 ActualOriginalNormalProfile318
open ActualOriginalGaussianMassRecovery318 ActualOriginalPositiveGraphIntegral318
open ActualOriginalGraphMassNormalization318 ActualOriginalAmbientFourierIdentity318
open ActualOriginalUndampedIntegrability318 ActualOriginalRealGoodRegion318
open MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 16000000

/-- The ordinary, undamped, absolutely convergent original singular
integral. Its identity follows from actual Fourier inversion only AFTER
integrability of the exact original transform has been produced. -/
theorem actual_original_undamped_integral (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hWn : ∀ x, 0 ≤ W x)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) :
    (∫ t : ℝ, originalOscillation κ W t) = (graphMass κ W : ℂ) := by
  obtain ⟨hpc,hpk,hpn,hpi,hzero⟩ :=
    actual_profile_properties κ η hη W hW.continuous hWc hWn hb
  have hpcc : Continuous (complexProfile κ W) := Complex.continuous_ofReal.comp hpc
  have hpck : HasCompactSupport (complexProfile κ W) := by
    apply hpk.mono
    intro s hs hzero
    apply hs
    simp only [complexProfile,hzero,Complex.ofReal_zero]
  have hpci : Integrable (complexProfile κ W) :=
    hpcc.integrable_of_hasCompactSupport hpck
  have he : originalOscillation κ W = 𝓕 (complexProfile κ W) := by
    funext t
    exact actual_original_ambient_fourier_identity κ η hη W hW.continuous hWc hb t
  have hfi : Integrable (𝓕 (complexProfile κ W)) := by
    rw [←he]
    exact actual_original_oscillation_integrable κ η hη W hW hWc hb
  have hinv := congrFun (hpcc.fourierInv_fourier_eq hpci hfi) (0 : ℝ)
  rw [Real.fourierInv_eq'] at hinv
  simp only [inner_zero_right,mul_zero,Complex.ofReal_zero,zero_mul,
    Complex.exp_zero,one_smul,complexProfile,hzero] at hinv
  rw [he]
  exact hinv

/-- One and the SAME produced original weight has absolute frequency
integrability and ordinary singular integral exactly ONE. All original
prime-form support and gradient inequalities are retained. -/
theorem actual_original_normalized_undamped_input {J : Type*} [Fintype J]
    (κ : ℝ) (hκ : 0 < κ) (γ : J → ℝ) :
    ∃ (x : Coordinates ℝ) (W : Coordinates ℝ → ℝ) (η : ℝ),
      equation κ x = 0 ∧ 0 < x.1.1 ∧ 0 < η ∧ HasCompactSupport W ∧
      ContDiff ℝ ∞ W ∧ (∀ y, 0 ≤ W y) ∧ 0 < W x ∧
      (∀ y ∈ tsupport W, y ∈ region γ ∧ η < ActualQuadricTaylor318.gradient κ y 0) ∧
      graphMass κ W = 1 ∧ Integrable (originalOscillation κ W) ∧
      (∫ t : ℝ, originalOscillation κ W t) = 1 := by
  obtain ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWn,hWx,hWs,hInt,hMass⟩ :=
    actual_original_normalized_graph_weight κ hκ γ
  have hb := fun y hy => (hWs y hy).2
  refine ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWn,hWx,hWs,hMass,
    actual_original_oscillation_integrable κ η hη W hWd hWc hb,?_⟩
  rw [actual_original_undamped_integral κ η hη W hWd hWc hWn hb,hMass]
  exact Complex.ofReal_one

end ActualOriginalUndampedSingularIntegral318
