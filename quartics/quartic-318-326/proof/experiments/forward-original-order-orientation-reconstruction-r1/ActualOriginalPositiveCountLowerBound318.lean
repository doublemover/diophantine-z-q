module
public import ActualOriginalBoundedPrimitiveMass318
public section
noncomputable section
namespace ActualOriginalPositiveCountLowerBound318
open Filter
open scoped Topology

/-- A positive actual normalized complex count limit supplies an eventual
lower bound on the norm of that SAME unnormalized count. -/
lemma actual_positive_count_norm_lower (Z : ℕ → ℂ) (B : ℕ → ℝ)
    (hB : ∀ n,0<B n) (S : ℝ) (hS : 0<S)
    (h : Tendsto (fun n => Z n/(B n : ℂ)^3) atTop (𝓝 (S : ℂ))) :
    ∀ᶠ n in atTop, (S/2)*(B n)^3≤‖Z n‖ := by
  have hn : Tendsto (fun n => ‖Z n/(B n : ℂ)^3‖) atTop (𝓝 S) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS] using h.norm
  have hl := hn.eventually (eventually_gt_nhds (show S/2<S by linarith))
  filter_upwards [hl] with n hn
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hB n)] at hn
  exact (le_div_iff₀ (pow_pos (hB n) 3)).mp hn.le
end ActualOriginalPositiveCountLowerBound318
