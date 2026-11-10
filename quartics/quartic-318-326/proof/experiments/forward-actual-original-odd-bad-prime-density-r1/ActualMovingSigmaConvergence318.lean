module
public import ActualComplexEulerReal318
public section
noncomputable section
namespace ActualMovingSigmaConvergence318
open scoped Topology
open Filter ActualMovingBoundaryPrimeTail318 ActualModFourSieveCharacter318
open ActualModFourLFunctionBoundary318
set_option maxHeartbeats 16000000

lemma actual_delta_limit : Tendsto delta atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  have hi := tendsto_inv_atTop_zero.comp hl
  simpa only [delta,one_div,Function.comp_def] using hi
lemma actual_sigma_limit : Tendsto sigma atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add actual_delta_limit
  simpa only [sigma,add_zero] using hh
lemma actual_complex_sigma_limit : Tendsto (fun N : ℕ => (sigma N:ℂ)) atTop (𝓝 1) := by
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp actual_sigma_limit
  simpa only [Complex.ofReal_one,Function.comp_def] using hh

/-- A single threshold for the actual L-function boundary norm, chosen
before any finite prime tail or later Euler truncation. -/
theorem actual_moving_L_lower :
    ∃ N₀ : ℕ,2≤N₀ ∧ ∀ N,N₀≤N →
      boundarySize/2≤‖DirichletCharacter.LFunction complexCharacter (sigma N:ℂ)‖ := by
  have he := actual_complex_sigma_limit.eventually actual_boundary_control
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  refine ⟨max 2 N₀,le_max_left _ _,?_⟩
  intro N hN
  exact ((hN₀ N ((le_max_right _ _).trans hN)).1).le

end ActualMovingSigmaConvergence318
