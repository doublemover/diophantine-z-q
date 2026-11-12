module
public import ActualOriginalNormalProfile318
public import Mathlib.Analysis.Fourier.Inversion
public section
noncomputable section
namespace ActualOriginalGaussianMassRecovery318
open QuadricCRTAssembly318 ActualOriginalNormalProfile318 ActualOriginalPositiveGraphIntegral318
open ActualOriginalGraphMassNormalization318 ActualOriginalRealGoodRegion318 Filter MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 16000000

@[expose] def complexProfile (κ : ℝ) (W : Coordinates ℝ→ℝ) (s : ℝ) : ℂ :=
  (normalProfile κ W s:ℂ)
/-- This is precisely the proved Mathlib one-dimensional Gaussian
approximate-identity normalization. No unproved exchange of improper
Fourier integrals is built into this definition. -/
@[expose] def gaussianRecovery (κ : ℝ) (W : Coordinates ℝ→ℝ) (c : ℝ) : ℂ :=
  ∫s : ℝ, ((Real.pi*c:ℂ)^(Module.finrank ℝ ℝ/2:ℂ)*
    Complex.exp (-Real.pi^2*c*‖(0:ℝ)-s‖^2)) • complexProfile κ W s

lemma actual_gaussian_recovers_mass (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W) (hWn : ∀x,0≤W x)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    Tendsto (gaussianRecovery κ W) atTop (𝓝 (graphMass κ W:ℂ)) := by
  obtain ⟨hpc,hpk,hpn,hpi,hzero⟩ := actual_profile_properties κ η hη W hW hWc hWn hb
  have hc : Continuous (complexProfile κ W) := Complex.continuous_ofReal.comp hpc
  have hk : HasCompactSupport (complexProfile κ W) := by
    apply hpk.mono
    intro s hs hh
    apply hs
    change (normalProfile κ W s:ℂ)=0
    rw [hh]
    norm_num
  have hi : Integrable (complexProfile κ W) := hc.integrable_of_hasCompactSupport hk
  have ht := Real.tendsto_integral_gaussian_smul' (f:=complexProfile κ W) (v:=(0:ℝ)) hi hc.continuousAt
  change Tendsto (gaussianRecovery κ W) atTop (𝓝 (complexProfile κ W 0)) at ht
  simpa only [complexProfile,hzero] using ht

/-- Actual normalization of the original smooth weight gives recovery
limit1 from the same original normal-coordinate profile. Identifying its
Fourier transform with the original oscillatory ambient integral still
requires the original change-of-variables proof; none is assumed here. -/
theorem actual_original_normalized_gaussian_recovery {J : Type*} [Fintype J]
    (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃(x : Coordinates ℝ) (W : Coordinates ℝ→ℝ) (η : ℝ),
      equation κ x=0 ∧ 0<x.1.1 ∧ 0<η ∧ HasCompactSupport W ∧
      ContDiff ℝ ∞ W ∧ (∀y,0≤W y) ∧ 0<W x ∧
      (∀y∈tsupport W,y∈region γ ∧ η<ActualQuadricTaylor318.gradient κ y 0) ∧
      graphMass κ W=1 ∧ Tendsto (gaussianRecovery κ W) atTop (𝓝 (1:ℂ)) := by
  obtain ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWn,hWx,hWs,hInt,hMass⟩ :=
    actual_original_normalized_graph_weight κ hκ γ
  have hrec := actual_gaussian_recovers_mass κ η hη W hWd.continuous hWc hWn
    (fun y hy => (hWs y hy).2)
  refine ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWn,hWx,hWs,hMass,?_⟩
  simpa only [hMass,Complex.ofReal_one] using hrec

end ActualOriginalGaussianMassRecovery318
