module
public import ActualOriginalNonzeroModeSum318
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public section
noncomputable section
namespace ActualOriginalRationalArcError318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCoordinateFrequency318
open ActualOriginalScaledCircle318 ActualOriginalRationalPoisson318 ActualOriginalZeroModeScaling318
open ActualOriginalScaledNonzeroModeBound318 ActualOriginalNonzeroModeSum318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- Removing the actual zero frequency from the absolutely convergent
original Poisson series gives precisely the difference from zeroModeArc. -/
lemma actual_rational_arc_remainder (κ : ℕ) (q : ℕ) [NeZero q] (hq : 0 < q)
    (a : ℤ) (β B : ℝ) (hB : 0 < B) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hs : Summable (fun m : Coordinates ℤ =>
      ‖nonzeroDualTerm κ q a (B/(q : ℝ)) (β*B^2) W m‖)) :
    scaledCircleSum (κ : ℤ) ((a : ℝ)/(q : ℝ)+β) B W -
      zeroModeArc (κ : ℤ) q a β B W =
      ∑' m : Coordinates ℤ, nonzeroDualTerm κ q a (B/(q : ℝ)) (β*B^2) W m := by
  classical
  let F := scaledDualTerm κ q a (B/(q : ℝ)) (β*B^2) W
  have hF : Summable F := by
    have hu := hs.of_norm.update (0 : Coordinates ℤ) (F 0)
    apply hu.congr
    intro m
    by_cases hm : m=0
    · simp [hm,F]
    · simp [Function.update,hm,nonzeroDualTerm,F]
  have he := hF.tsum_eq_add_tsum_ite (0 : Coordinates ℤ)
  rw [actual_original_rational_poisson (κ : ℤ) q hq a β B hB W hW hWc]
  change (∑' m : Coordinates ℤ, F m) - zeroModeArc (κ : ℤ) q a β B W = _
  rw [he]
  have hz : F 0 = zeroModeArc (κ : ℤ) q a β B W := by
    simp only [F,scaledDualTerm,integerEmbed_zero,smul_zero,zeroModeArc]
  rw [hz,add_sub_cancel_left]
  rfl

/-- Quantitative uniform error in the ACTUAL rational-arc circle sum.
Both arithmetic and analytic bounds are consumed: the complete coefficient
contributes sqrt(32*kappa*q^5), and full nonzero summation leaves q/B.
Constants precede q, unit numerator, B and beta. -/
theorem actual_original_rational_arc_error (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], ∀ a : ℤ,
      IsUnit (a : ZMod q) → ∀ (β B : ℝ), 0 < B →
      ‖scaledCircleSum (κ : ℤ) ((a : ℝ)/(q : ℝ)+β) B W -
        zeroModeArc (κ : ℤ) q a β B W‖ ≤
        (Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*C*(1+‖β*B^2‖)^k*(q : ℝ)/B)*latticeSixthMass := by
  obtain ⟨k,C,hC,hbound⟩ := actual_nonzero_series_bound κ hκ W hW hWc
  refine ⟨k,C,hC,fun q _ a ha β B hB => ?_⟩
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  obtain ⟨hs,herr⟩ := hbound q a ha (B/(q : ℝ)) (β*B^2) (div_pos hB hqr)
  rw [actual_rational_arc_remainder κ q hq a β B hB W hW hWc hs]
  convert herr using 1 <;> field_simp [hB.ne',hqr.ne'] <;> ring

end ActualOriginalRationalArcError318
