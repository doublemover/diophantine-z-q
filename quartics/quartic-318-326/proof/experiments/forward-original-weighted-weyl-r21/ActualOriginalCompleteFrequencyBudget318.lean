module
public import ActualOriginalFrequencyBlockPartition318
public section
noncomputable section
namespace ActualOriginalCompleteFrequencyBudget318
open ActualOriginalFrequencyBlockPartition318 ActualOriginalReciprocalBinBudget318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalWeightedBlockReciprocalBudget318
open scoped BigOperators

@[expose] def reciprocalBlockBudget (N : ℝ) (q : ℤ) : ℝ :=
  ∑ b∈Finset.Icc (-q) q, binCost N q b

lemma actual_reciprocal_block_budget_nonneg (N : ℝ) (q : ℤ) (hN : 0≤N) (hq : 0<q) :
    0≤reciprocalBlockBudget N q :=
  Finset.sum_nonneg (fun b hb => actual_bin_cost_nonneg N q b hN hq)

/-- An arbitrary finite frequency set is partitioned completely into
controlled blocks, and every resonance and incomplete edge block is retained. -/
theorem actual_complete_frequency_budget (a q L : ℤ) (s : Finset ℤ) (t N : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hL : 0<L) (hshort : 2*(L-1)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (hN : 0≤N) :
    (∑ c∈s, fourierChordCap N c t)≤
      ((blockKeys L s).card : ℝ)*reciprocalBlockBudget N q := by
  rw [actual_frequency_block_partition L s]
  calc
    _ ≤ ∑ k∈blockKeys L s, reciprocalBlockBudget N q := by
      apply Finset.sum_le_sum
      intro k hk
      have hsub := actual_block_fiber_subset L s k hL
      have hsmall : 2*((k*L+L-1)-(k*L))≤q := by omega
      apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun c hc hnot => actual_chord_cap_nonneg N c t hN)).trans
      exact actual_rational_short_block_chord_budget a q (k*L) (k*L+L-1) t N
        hq ha hsmall ht hN
    _ = _ := by simp [nsmul_eq_mul]

/-- A produced block length and an explicit endpoint-count bound now
control the COMPLETE original frequency interval, not just one short block. -/
theorem actual_complete_interval_frequency_budget (a q lo hi : ℤ) (t N : ℝ)
    (hq : 0<q) (ha : IsCoprime q a)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (hN : 0≤N) :
    (∑ c∈Finset.Icc lo hi, fourierChordCap N c t)≤
      ((hi/rationalBlockLength q-lo/rationalBlockLength q+1).toNat : ℝ)*
        reciprocalBlockBudget N q := by
  obtain ⟨hL,hshort⟩ := actual_rational_block_length q hq
  apply (actual_complete_frequency_budget a q (rationalBlockLength q)
    (Finset.Icc lo hi) t N hq ha hL hshort ht hN).trans
  apply mul_le_mul_of_nonneg_right _ (actual_reciprocal_block_budget_nonneg N q hN hq)
  exact_mod_cast actual_frequency_block_count (rationalBlockLength q) lo hi
    (Finset.Icc lo hi) hL (by intro c hc; exact hc)

end ActualOriginalCompleteFrequencyBudget318
