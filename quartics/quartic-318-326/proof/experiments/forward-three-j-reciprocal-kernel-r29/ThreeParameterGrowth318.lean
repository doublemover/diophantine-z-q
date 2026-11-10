module
public import ThreeCompactParameter318
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.Basic
public section
noncomputable section
open Filter Topology
namespace ThreeParameterGrowth318
open ThreeCompactParameter318
set_option maxHeartbeats 0

/-- The independently specified rational j-function bounds its parameter at
infinity. This uniform estimate does not choose a branch of the inverse map. -/
theorem norm_le_j (t : ℂ) (ht : t ≠ 0) : ‖t‖ ≤ 486 + 16 * ‖J t‖ := by
  by_cases hs : ‖t‖ ≤ 486
  · nlinarith [norm_nonneg (J t)]
  have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have h27 : ‖t‖/2 ≤ ‖t+27‖ := by
    have h := norm_sub_le (t+27) (27:ℂ)
    norm_num at h
    nlinarith
  have h243 : ‖t‖/2 ≤ ‖t+243‖ := by
    have h := norm_sub_le (t+243) (243:ℂ)
    norm_num at h
    nlinarith
  have hm : (‖t‖/2)^4 ≤ ‖t+27‖ * ‖t+243‖^3 := by
    calc
      (‖t‖/2)^4 = (‖t‖/2) * (‖t‖/2)^3 := by ring
      _ ≤ ‖t+27‖ * ‖t+243‖^3 :=
        mul_le_mul h27 (pow_le_pow_left₀ (by positivity) h243 3) (by positivity) (norm_nonneg _)
  have hj : ‖J t‖ * ‖t‖^3 = ‖t+27‖ * ‖t+243‖^3 := by
    rw [J, norm_div, norm_mul, norm_pow, norm_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hpos.ne')
  rw [←hj] at hm
  have hbound : ‖t‖ ≤ 16 * ‖J t‖ := by
    have hc : (‖t‖ - 16 * ‖J t‖) * ‖t‖^3 ≤ 0 := by nlinarith [hm]
    by_contra hb
    have hp : 0 < ‖t‖ - 16 * ‖J t‖ := by linarith
    have := mul_pos hp (pow_pos hpos 3)
    linarith
  linarith

/-- Polynomial growth of a holomorphic punctured germ gives actual meromorphy.
Multiplication by one additional power forces a continuous zero, so the weak
removable-singularity theorem applies to the original function's own germ. -/
theorem meromorphic_of_polynomial_bound {f : ℂ → ℂ} (n : ℕ) (C : ℝ)
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z)
    (hb : ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖z^n * f z‖ ≤ C) : MeromorphicAt f 0 := by
  let F : ℂ → ℂ := fun z => z^(n+1) * f z
  have hF0 : F 0 = 0 := by simp [F]
  have ht : Tendsto F (𝓝[≠] 0) (𝓝 0) := by
    apply squeeze_zero_norm'
      (a:=fun z : ℂ => ‖z‖ * C)
    · filter_upwards [hb] with z hz
      calc
        ‖F z‖ = ‖z‖ * ‖z^n * f z‖ := by simp [F,pow_succ',mul_assoc]
        _ ≤ ‖z‖ * C := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    · simpa using ((continuousAt_id : ContinuousAt (fun z : ℂ => z) 0).norm.tendsto.mono_left nhdsWithin_le_nhds).mul_const C
  have hc : ContinuousAt F 0 := by
    rw [←continuousWithinAt_compl_self]
    change Tendsto F (𝓝[≠] 0) (𝓝 (F 0))
    rw [hF0]
    exact ht
  have ha : AnalyticAt ℂ F 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (hd.mono fun z hz => ((differentiableAt_id.pow _).mul hz)) hc
  exact ⟨n+1,by simpa [F,sub_zero,smul_eq_mul] using ha⟩

end ThreeParameterGrowth318
