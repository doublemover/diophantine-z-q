module
public import ActualOriginalUniformFullDualDecay318
public section
noncomputable section
namespace ActualOriginalScaledNonzeroModeBound318
open QuadricCRTAssembly318 ActualOriginalCompleteSumBound318 ActualOriginalRationalPoisson318
open ActualOriginalCoordinateFrequency318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318 ActualOriginalUniformFullDualDecay318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- The square-root bound is for the literal complete coefficient, even
at bad primes and even moduli. The radicand is retained without rounding. -/
lemma actual_complete_arc_norm_bound (κ : ℕ) (hκ : 0 < κ)
    (q : ℕ) [NeZero q] (a : ℤ) (ha : IsUnit (a : ZMod q)) (m : Coordinates ℤ) :
    ‖completeArcCoefficient (κ : ℤ) q a m‖ ≤ Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5) := by
  have h := actual_complete_arc_square_bound κ hκ q a ha m
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 32*(κ : ℝ)*(q : ℝ)^5 by positivity)
  have hn := Real.sqrt_nonneg (32*(κ : ℝ)*(q : ℝ)^5)
  nlinarith [norm_nonneg (completeArcCoefficient (κ : ℤ) q a m)]

/-- Literal scaled full-frequency Poisson summand. The variable t is
the actual rescaled beta parameter beta*B^2 in the rational-arc formula. -/
@[expose] def scaledDualTerm (κ : ℕ) (q : ℕ) [NeZero q] (a : ℤ)
    (R t : ℝ) (W : Coordinates ℝ → ℝ) (m : Coordinates ℤ) : ℂ :=
  completeArcCoefficient (κ : ℤ) q a m *
    (R^5 • originalCoordinateFourier (κ : ℝ) t W (R • integerEmbed m))

/-- The actual fifth power of ambient scaling cancels against sixth
order Fourier decay. Every nonzero original integer dual vector has a
uniform inverse-sixth majorant with the explicit residual factor R^-1. -/
theorem actual_nonzero_mode_bound (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], ∀ a : ℤ,
      IsUnit (a : ZMod q) → ∀ (R t : ℝ), 0 < R → ∀ m : Coordinates ℤ, m ≠ 0 →
      ‖scaledDualTerm κ q a R t W m‖ ≤
        (Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*C*(1+‖t‖)^k/R) * (‖integerEmbed m‖⁻¹)^6 := by
  obtain ⟨k,C,hC,hdecay⟩ := actual_uniform_coordinate_decay (κ : ℝ) W hW hWc 6
  refine ⟨k,C,hC,fun q _ a ha R t hR m hm => ?_⟩
  have hem : integerEmbed m ≠ 0 := by
    intro he
    apply hm
    apply actual_integer_embedding_closed.injective
    simpa only [integerEmbed_zero] using he
  have hn : 0 < ‖integerEmbed m‖ := norm_pos_iff.mpr hem
  have hnorm : ‖R • integerEmbed m‖ = R*‖integerEmbed m‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
  have hF : ‖originalCoordinateFourier (κ : ℝ) t W (R • integerEmbed m)‖ ≤
      (C*(1+‖t‖)^k)/((R*‖integerEmbed m‖)^6) := by
    apply (le_div_iff₀ (pow_pos (mul_pos hR hn) 6)).mpr
    have hh := hdecay t (R • integerEmbed m)
    rw [hnorm] at hh
    simpa only [mul_comm] using hh
  calc
    _ = ‖completeArcCoefficient (κ : ℤ) q a m‖ * R^5 *
        ‖originalCoordinateFourier (κ : ℝ) t W (R • integerEmbed m)‖ := by
      simp only [scaledDualTerm,norm_mul,norm_smul,Real.norm_eq_abs,
        abs_of_pos (pow_pos hR 5),mul_assoc]
    _ ≤ Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5) * R^5 *
        ((C*(1+‖t‖)^k)/((R*‖integerEmbed m‖)^6)) := by
      gcongr <;> first
        | exact actual_complete_arc_norm_bound κ hκ q a ha m
        | exact hF
    _ = _ := by
      field_simp [hR.ne',hn.ne']
      <;> ring

end ActualOriginalScaledNonzeroModeBound318
