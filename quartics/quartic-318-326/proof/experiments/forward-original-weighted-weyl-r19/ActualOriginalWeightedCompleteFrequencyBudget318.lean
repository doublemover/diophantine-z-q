module
public import ActualOriginalDisplacementBlockPartition318
public section
noncomputable section
namespace ActualOriginalWeightedCompleteFrequencyBudget318
open ActualOriginalCompleteFrequencyBudget318 ActualOriginalFrequencyBlockPartition318
open ActualOriginalWeightedLinearCancellation318 ActualOriginalFiniteAbel318
open ActualOriginalWeightedBlockReciprocalBudget318 ActualOriginalRationalBlockReciprocalSum318
open scoped BigOperators

/-- COMPLETE finite frequency sum, with arbitrary frequency-dependent
weights and starts. The explicit block count replaces a short-block premise;
the genuine uniform weight-variation requirement remains visible. -/
theorem actual_weighted_complete_frequency_budget (a q L : ℤ) (s : Finset ℤ) (t : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hL : 0<L) (hshort : 2*(L-1)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (g : ℤ → ℕ → ℂ) (m : ℤ → ℤ) (N : ℕ) (V : ℝ) (hV : 0≤V)
    (hv : ∀ c∈s, variation (g c) N≤V) :
    (∑ c∈s, ‖weightedLinearInterval c (m c) (g c) (N+1) (t : AddCircle (1 : ℝ))‖)≤
      V*(((blockKeys L s).card : ℝ)*reciprocalBlockBudget ((N : ℝ)+1) q) := by
  calc
    _ ≤ ∑ c∈s, fourierChordCap ((N : ℝ)+1) c t*V := by
      apply Finset.sum_le_sum
      intro c hc
      exact (actual_weighted_chord_cap c (m c) (g c) N t).trans
        (mul_le_mul_of_nonneg_left (hv c hc) (actual_chord_cap_nonneg _ c t (by positivity)))
    _ = (∑ c∈s, fourierChordCap ((N : ℝ)+1) c t)*V := by rw [Finset.sum_mul]
    _ ≤ (((blockKeys L s).card : ℝ)*reciprocalBlockBudget ((N : ℝ)+1) q)*V :=
      mul_le_mul_of_nonneg_right
        (actual_complete_frequency_budget a q L s t ((N : ℝ)+1) hq ha hL hshort ht (by positivity)) hV
    _ = _ := mul_comm _ _

end ActualOriginalWeightedCompleteFrequencyBudget318
