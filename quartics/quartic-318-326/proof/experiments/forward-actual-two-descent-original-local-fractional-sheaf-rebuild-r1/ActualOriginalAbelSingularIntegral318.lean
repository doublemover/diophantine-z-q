module
public import ActualOriginalGaussianFourierFlip318
public section
noncomputable section
namespace ActualOriginalAbelSingularIntegral318
open QuadricCRTAssembly318 ActualOriginalNormalProfile318 ActualOriginalGaussianMassRecovery318
open ActualOriginalPositiveGraphIntegral318 ActualOriginalGraphMassNormalization318
open ActualOriginalAmbientFourierIdentity318 ActualOriginalGaussianFourierFlip318
open ActualOriginalRealGoodRegion318 Filter MeasureTheory
open scoped Topology FourierTransform ContDiff
set_option maxHeartbeats 16000000

/-- The Abel-regularized ORIGINAL ambient oscillatory integral. -/
@[expose] def abelOriginalIntegral (κ : ℝ) (W : Coordinates ℝ→ℝ) (c : ℝ) : ℂ :=
  ∫t : ℝ,Complex.exp (-(c:ℂ)⁻¹*‖t‖^2) • originalOscillation κ W t

lemma actual_abel_equals_gaussian (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W) (hWn : ∀x,0≤W x)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0)
    (c : ℝ) (hc : 0<c) : abelOriginalIntegral κ W c=gaussianRecovery κ W c := by
  obtain ⟨hpc,hpk,hpn,hpi,hzero⟩ := actual_profile_properties κ η hη W hW hWc hWn hb
  have hpcc : Continuous (complexProfile κ W) := Complex.continuous_ofReal.comp hpc
  have hpck : HasCompactSupport (complexProfile κ W) := by
    apply hpk.mono
    intro s hs hh
    apply hs
    change (normalProfile κ W s:ℂ)=0
    rw [hh]
    norm_num
  have hpci : Integrable (complexProfile κ W) := hpcc.integrable_of_hasCompactSupport hpck
  unfold abelOriginalIntegral gaussianRecovery
  simp_rw [actual_original_ambient_fourier_identity κ η hη W hW hWc hb]
  exact actual_gaussian_fourier_flip (complexProfile κ W) hpci c hc

/-- The actual Abel-regularized singular integral of the ORIGINAL ambient
quadric converges to the exact positive graph mass. This is explicitly an
Abel statement, not an assertion of undamped Fourier integrability. -/
theorem actual_original_abel_limit (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W) (hWn : ∀x,0≤W x)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    Tendsto (abelOriginalIntegral κ W) atTop (𝓝 (graphMass κ W:ℂ)) := by
  apply (actual_gaussian_recovers_mass κ η hη W hW hWc hWn hb).congr'
  filter_upwards [Ioi_mem_atTop (0:ℝ)] with c hc
  exact (actual_abel_equals_gaussian κ η hη W hW hWc hWn hb c hc).symm

theorem actual_original_normalized_abel_input {J : Type*} [Fintype J]
    (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃(x : Coordinates ℝ) (W : Coordinates ℝ→ℝ) (η : ℝ),
      equation κ x=0 ∧ 0<x.1.1 ∧ 0<η ∧ HasCompactSupport W ∧
      ContDiff ℝ ∞ W ∧ (∀y,0≤W y) ∧ 0<W x ∧
      (∀y∈tsupport W,y∈region γ ∧ η<ActualQuadricTaylor318.gradient κ y 0) ∧
      graphMass κ W=1 ∧ Tendsto (abelOriginalIntegral κ W) atTop (𝓝 (1:ℂ)) := by
  obtain ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWn,hWx,hWs,hInt,hMass⟩ :=
    actual_original_normalized_graph_weight κ hκ γ
  have hrec := actual_original_abel_limit κ η hη W hWd.continuous hWc hWn
    (fun y hy => (hWs y hy).2)
  refine ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWn,hWx,hWs,hMass,?_⟩
  simpa only [hMass,Complex.ofReal_one] using hrec

end ActualOriginalAbelSingularIntegral318
