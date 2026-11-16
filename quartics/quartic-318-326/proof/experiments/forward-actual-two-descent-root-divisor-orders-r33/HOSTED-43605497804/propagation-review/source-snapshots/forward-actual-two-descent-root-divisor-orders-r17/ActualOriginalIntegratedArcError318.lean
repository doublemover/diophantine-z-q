module
public import ActualOriginalRationalArcError318
public section
noncomputable section
namespace ActualOriginalIntegratedArcError318
open QuadricCRTAssembly318 ActualOriginalScaledCircle318 ActualOriginalZeroModeScaling318
open ActualOriginalNonzeroModeSum318 ActualOriginalRationalArcError318
open MeasureTheory Set
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- The actual integral of the difference from the zero mode on one
symmetric original beta arc. No surrogate lattice sum is substituted. -/
@[expose] def integratedArcError (κ : ℕ) (q : ℕ) [NeZero q] (a : ℤ)
    (B T : ℝ) (W : Coordinates ℝ → ℝ) : ℂ :=
  ∫ β : ℝ in -T/B^2..T/B^2,
    scaledCircleSum (κ : ℤ) ((a : ℝ)/(q : ℝ)+β) B W - zeroModeArc (κ : ℤ) q a β B W

/-- Uniformly integrating the full Poisson remainder contributes the
actual arc length2T/B^2. The resulting error is O(B^-3), with all q,T
factors explicit and constants chosen before any rational arc. -/
theorem actual_integrated_arc_error (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], ∀ a : ℤ,
      IsUnit (a : ZMod q) → ∀ (B T : ℝ), 0 < B → 0 ≤ T →
      ‖integratedArcError κ q a B T W‖ ≤
        (2*T*Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*C*(1+T)^k*(q : ℝ)*latticeSixthMass)/B^3 := by
  obtain ⟨k,C,hC,herror⟩ := actual_original_rational_arc_error κ hκ W hW hWc
  refine ⟨k,C,hC,fun q _ a ha B T hB hT => ?_⟩
  have hB2 : 0 < B^2 := pow_pos hB 2
  have hends : -T/B^2 ≤ T/B^2 := div_le_div_of_nonneg_right (by linarith) hB2.le
  have hL := latticeSixthMass_nonneg
  let A : ℝ := (Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*C*(1+T)^k*(q : ℝ)/B)*latticeSixthMass
  have hp : ∀ β ∈ Set.uIoc (-T/B^2) (T/B^2),
      ‖scaledCircleSum (κ : ℤ) ((a : ℝ)/(q : ℝ)+β) B W - zeroModeArc (κ : ℤ) q a β B W‖ ≤ A := by
    intro β hβ
    rw [Set.uIoc_of_le hends] at hβ
    have hl : -T < β*B^2 := (div_lt_iff₀ hB2).mp hβ.1
    have hu : β*B^2 ≤ T := (le_div_iff₀ hB2).mp hβ.2
    have hn : ‖β*B^2‖ ≤ T := by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨hl.le,hu⟩
    refine (herror q a ha β B hB).trans ?_
    dsimp [A]
    gcongr <;> assumption
  have hlen : |T/B^2-(-T/B^2)| = 2*T/B^2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hends)]
    ring
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hp
  change ‖integratedArcError κ q a B T W‖ ≤ A*|T/B^2-(-T/B^2)| at hh
  rw [hlen] at hh
  convert hh using 1 <;> dsimp [A] <;> field_simp [hB.ne'] <;> ring

end ActualOriginalIntegratedArcError318
