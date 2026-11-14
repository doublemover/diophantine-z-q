module
public import ActualOriginalPolynomialMinorBound318
public section
noncomputable section
namespace ActualOriginalPolynomialMinorDecay318
open QuadricCRTAssembly318 ActualOriginalPolynomialMinorScale318 ActualOriginalPolynomialMinorBound318
open ActualOriginalCircleMinorArcIdentity318 Filter
open scoped Topology ContDiff

lemma actual_polynomial_inverse_limit (K : ℝ) :
    Tendsto (fun n : ℕ => K/((n+2 : ℕ) : ℝ)^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n : ℕ => show (n : ℝ)≤((n+2 : ℕ) : ℝ) by push_cast; linarith)
    exact tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hn
  have hh := hi.pow 2
  have hc := hh.const_mul K
  simpa only [div_eq_mul_inv,inv_pow,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero] using hc

/-- Genuine normalized minor decay for the displayed common cutoff and
scale sequence. This is not yet a major+minor theorem: the older major
result's arbitrary-fast diagonal has NOT been identified with this one. -/
theorem actual_polynomial_minor_decay (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    Tendsto (fun n : ℕ => minorArcIntegral κ (minorCutoff (n+2)) (minorScale (n+2)) W /
      (minorScale (n+2) : ℂ)^3) atTop (𝓝 0) := by
  obtain ⟨K,hK,hb⟩ := actual_polynomial_minor_normalized_bound κ hκ W hW hc
  exact squeeze_zero_norm (fun n => hb (n+2) (by omega)) (actual_polynomial_inverse_limit K)

/-- Both the actual cutoff and the actual scale grow; the geometric
major-arc separation condition holds on the SAME sequence at every stage. -/
theorem actual_polynomial_scale_properties :
    Tendsto (fun n : ℕ => minorCutoff (n+2)) atTop atTop ∧
    Tendsto (fun n : ℕ => minorScale (n+2)) atTop atTop ∧
    (∀ n : ℕ, ((minorCutoff (n+2) : ℝ)+1)^3≤minorScale (n+2)) := by
  have hcut (n : ℕ) : n≤minorCutoff (n+2) := by
    have hx : (1 : ℝ)≤((n+2 : ℕ) : ℝ) := by push_cast; positivity
    have hh := actual_power_degree_mono ((n+2 : ℕ) : ℝ) hx 1 8 (by omega)
    simp only [pow_one] at hh
    have hh' : n+2≤(n+2)^8 := by exact_mod_cast hh
    exact (Nat.le_add_right n 2).trans hh'
  have hscale (n : ℕ) : (n : ℝ)≤minorScale (n+2) := by
    have hx : (1 : ℝ)≤((n+2 : ℕ) : ℝ) := by push_cast; positivity
    have hh := actual_power_degree_mono ((n+2 : ℕ) : ℝ) hx 1 32 (by omega)
    simp only [pow_one] at hh
    exact (show (n : ℝ)≤((n+2 : ℕ) : ℝ) by push_cast; linarith).trans hh
  exact ⟨tendsto_atTop_mono hcut tendsto_id,
    tendsto_atTop_mono hscale tendsto_natCast_atTop_atTop,
    fun n => (actual_polynomial_minor_scale (n+2) (by omega)).2.2⟩

end ActualOriginalPolynomialMinorDecay318
