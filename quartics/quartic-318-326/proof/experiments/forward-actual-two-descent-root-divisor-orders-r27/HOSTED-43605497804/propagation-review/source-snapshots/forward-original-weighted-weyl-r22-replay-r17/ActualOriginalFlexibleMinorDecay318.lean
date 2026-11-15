module
public import ActualOriginalFlexibleMinorBound318
public section
noncomputable section
namespace ActualOriginalFlexibleMinorDecay318
open ActualOriginalPolynomialMinorScale318 ActualOriginalPolynomialMinorDecay318
open QuadricCRTAssembly318 ActualOriginalFlexibleMinorScale318 ActualOriginalFlexibleMinorBound318
open ActualOriginalCircleMinorArcIdentity318 Filter
open scoped Topology ContDiff

/-- The parameter p and hence the divisor exponent are fixed BEFORE n.
This flexible family permits a later choice from the major-error exponent. -/
theorem actual_flexible_minor_decay (p : ℕ) (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    Tendsto (fun n : ℕ => minorArcIntegral κ (minorCutoff (n+2)) (flexibleScale p (n+2)) W /
      (flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 0) := by
  obtain ⟨K,hK,hb⟩ := actual_flexible_minor_normalized_bound p κ hκ W hW hc
  exact squeeze_zero_norm (fun n => hb (n+2) (by omega)) (actual_polynomial_inverse_limit K)

lemma actual_flexible_scale_properties (p : ℕ) :
    Tendsto (fun n : ℕ => minorCutoff (n+2)) atTop atTop ∧
    Tendsto (fun n : ℕ => flexibleScale p (n+2)) atTop atTop ∧
    (∀ n : ℕ, ((minorCutoff (n+2) : ℝ)+1)^3≤flexibleScale p (n+2)) := by
  have hscale (n : ℕ) : minorScale (n+2)≤flexibleScale p (n+2) :=
    actual_power_degree_mono ((n+2 : ℕ) : ℝ) (by push_cast; positivity) 32 (p*8+32) (by omega)
  exact ⟨actual_polynomial_scale_properties.1,
    tendsto_atTop_mono hscale actual_polynomial_scale_properties.2.1,
    fun n => (actual_flexible_minor_scale p (n+2) (by omega)).2.2⟩

end ActualOriginalFlexibleMinorDecay318
