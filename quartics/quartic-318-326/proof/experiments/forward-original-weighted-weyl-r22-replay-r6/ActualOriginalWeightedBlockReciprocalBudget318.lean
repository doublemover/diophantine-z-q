module
public import ActualOriginalRationalBlockReciprocalSum318
public section
noncomputable section
namespace ActualOriginalWeightedBlockReciprocalBudget318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalReciprocalBinBudget318
open ActualOriginalWeightedLinearCancellation318 ActualOriginalFiniteAbel318
open scoped BigOperators

lemma actual_chord_cap_nonneg (N : ℝ) (c : ℤ) (t : ℝ) (hN : 0≤N) :
    0≤fourierChordCap N c t := by
  unfold fourierChordCap
  split_ifs
  · exact hN
  · exact le_min hN (by positivity)

/-- The actual arbitrary-weight interval consumes the exact same kernel
in both resonant and nonresonant cases, with no missing exceptional term. -/
theorem actual_weighted_chord_cap (c m : ℤ) (g : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖weightedLinearInterval c m g (N+1) (t : AddCircle (1 : ℝ))‖≤
      fourierChordCap ((N : ℝ)+1) c t*variation g N := by
  by_cases h : fourier c (t : AddCircle (1 : ℝ))=1
  · rw [fourierChordCap,if_pos h]
    exact actual_weighted_linear_length_bound c m g N _
  · rw [fourierChordCap,if_neg h]
    exact actual_weighted_linear_cancellation c m g N _ h

/-- A COMPLETE short block of genuinely arbitrary frequency-dependent
weights is controlled by the produced reciprocal-bin budget, given their
actual uniform variation bound. This is not a separable-weight assertion. -/
theorem actual_weighted_short_block_budget (a q lo hi : ℤ) (t : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hdiam : 2*(hi-lo)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (g : ℤ → ℕ → ℂ) (m : ℤ → ℤ) (N : ℕ) (V : ℝ) (hV : 0≤V)
    (hv : ∀ c∈Finset.Icc lo hi, variation (g c) N≤V) :
    (∑ c∈Finset.Icc lo hi,
      ‖weightedLinearInterval c (m c) (g c) (N+1) (t : AddCircle (1 : ℝ))‖)≤
      V*(∑ b∈Finset.Icc (-q) q, binCost ((N : ℝ)+1) q b) := by
  calc
    _ ≤ ∑ c∈Finset.Icc lo hi, fourierChordCap ((N : ℝ)+1) c t*V := by
      apply Finset.sum_le_sum
      intro c hc
      exact (actual_weighted_chord_cap c (m c) (g c) N t).trans
        (mul_le_mul_of_nonneg_left (hv c hc) (actual_chord_cap_nonneg _ c t (by positivity)))
    _ = (∑ c∈Finset.Icc lo hi, fourierChordCap ((N : ℝ)+1) c t)*V := by
      rw [Finset.sum_mul]
    _ ≤ (∑ b∈Finset.Icc (-q) q, binCost ((N : ℝ)+1) q b)*V :=
      mul_le_mul_of_nonneg_right
        (actual_rational_short_block_chord_budget a q lo hi t ((N : ℝ)+1) hq ha hdiam ht (by positivity)) hV
    _ = _ := mul_comm _ _

end ActualOriginalWeightedBlockReciprocalBudget318
