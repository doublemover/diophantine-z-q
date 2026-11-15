module
public import ActualOriginalWeightedBlockReciprocalBudget318
public section
noncomputable section
namespace ActualOriginalFrequencyBlockPartition318
open scoped BigOperators

@[expose] def blockKeys (L : ℤ) (s : Finset ℤ) : Finset ℤ := s.image (fun c => c/L)
@[expose] def blockFiber (L : ℤ) (s : Finset ℤ) (k : ℤ) : Finset ℤ :=
  s.filter (fun c => c/L=k)
@[expose] def rationalBlockLength (q : ℤ) : ℤ := q/2+1

lemma actual_rational_block_length (q : ℤ) (hq : 0<q) :
    0<rationalBlockLength q ∧ 2*(rationalBlockLength q-1)≤q := by
  unfold rationalBlockLength
  omega

/-- Euclidean quotient blocks cover positive AND negative frequencies,
with exactly the same integer interval convention. -/
lemma actual_frequency_in_quotient_block (L c : ℤ) (hL : 0<L) :
    c∈Finset.Icc ((c/L)*L) ((c/L)*L+L-1) := by
  have hlo := Int.ediv_mul_le c (ne_of_gt hL)
  have hhi := Int.lt_ediv_mul c hL
  apply Finset.mem_Icc.mpr
  omega

lemma actual_block_fiber_subset (L : ℤ) (s : Finset ℤ) (k : ℤ) (hL : 0<L) :
    blockFiber L s k⊆Finset.Icc (k*L) (k*L+L-1) := by
  intro c hc
  have he := (Finset.mem_filter.mp hc).2
  have hb := actual_frequency_in_quotient_block L c hL
  rwa [he] at hb

/-- Exact disjoint finite partition, not a separately chosen covering
or omitted endpoint remainder. Every original frequency occurs once. -/
theorem actual_frequency_block_partition (L : ℤ) (s : Finset ℤ) (f : ℤ → ℝ) :
    (∑ c∈s, f c)=∑ k∈blockKeys L s, ∑ c∈blockFiber L s k, f c := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun c hc => Finset.mem_image_of_mem (fun c => c/L) hc) f

/-- Actual block count is bounded by the explicit quotient endpoint
interval. Empty original sets do not require a nonempty interval premise. -/
lemma actual_frequency_block_count (L lo hi : ℤ) (s : Finset ℤ) (hL : 0<L)
    (hs : s⊆Finset.Icc lo hi) :
    (blockKeys L s).card≤(hi/L-lo/L+1).toNat := by
  have hsub : blockKeys L s⊆Finset.Icc (lo/L) (hi/L) := by
    intro k hk
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hk
    have hc' := Finset.mem_Icc.mp (hs hc)
    exact Finset.mem_Icc.mpr ⟨Int.ediv_le_ediv hL hc'.1,Int.ediv_le_ediv hL hc'.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  omega

end ActualOriginalFrequencyBlockPartition318
