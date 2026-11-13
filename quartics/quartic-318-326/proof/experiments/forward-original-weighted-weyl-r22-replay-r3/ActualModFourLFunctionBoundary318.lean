module
public import ActualModFourSieveCharacter318
public section
noncomputable section
namespace ActualModFourLFunctionBoundary318
open scoped BigOperators Topology
open Filter ActualModFourSieveCharacter318
set_option maxHeartbeats 16000000

@[expose] def boundarySize : ℝ := ‖DirichletCharacter.LFunction complexCharacter 1‖
lemma boundary_size_pos : 0<boundarySize := norm_pos_iff.mpr original_character_L_nonzero

/-- The original mod-four L-function has genuine two-sided norm control
in a neighborhood of1. The size is its actual nonzero boundary value. -/
theorem actual_boundary_control :
    ∀ᶠ s : ℂ in 𝓝 1,
      boundarySize/2<‖DirichletCharacter.LFunction complexCharacter s‖ ∧
      ‖DirichletCharacter.LFunction complexCharacter s‖<2*boundarySize := by
  have hc : ContinuousAt (fun s : ℂ => ‖DirichletCharacter.LFunction complexCharacter s‖) 1 :=
    (DirichletCharacter.differentiable_LFunction character_nontrivial).continuous.continuousAt.norm
  have hlow : boundarySize/2<boundarySize := by linarith [boundary_size_pos]
  have hhigh : boundarySize<2*boundarySize := by linarith [boundary_size_pos]
  exact hc.tendsto.eventually (Ioo_mem_nhds hlow hhigh)

/-- The actual finite Euler products converge to this same L-function
for every real sigma>1. This identifies the product before any boundary
comparison or tail estimate is attempted. -/
theorem actual_euler_limit (σ : ℝ) (hσ : 1<σ) :
    Tendsto (fun n : ℕ => ∏ p∈Nat.primesBelow n,
      (1-complexCharacter (p:ZMod 4)*(p:ℂ)^(-(σ:ℂ)))⁻¹) atTop
      (𝓝 (DirichletCharacter.LFunction complexCharacter (σ:ℂ))) := by
  have hs : 1<(σ:ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries complexCharacter hs]
  exact complexCharacter.LSeries_eulerProduct hs

/-- The factors in that genuine Dirichlet Euler product use EXACTLY
the original real character values, not a separately chosen sign pattern. -/
theorem actual_euler_factor (σ : ℝ) (p : ℕ) :
    (1-complexCharacter (p:ZMod 4)*(p:ℂ)^(-(σ:ℂ)))⁻¹=
      (1-(realCharacter p:ℂ)*(p:ℂ)^(-(σ:ℂ)))⁻¹ := by
  rw [complex_character_value]

end ActualModFourLFunctionBoundary318
