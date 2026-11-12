module
public import ActualOriginalWeightedCompleteFrequencyBudget318
public section
noncomputable section
namespace ActualOriginalEvenDisplacementFrequencyBudget318
open ActualOriginalCompleteFrequencyBudget318 ActualOriginalFrequencyBlockPartition318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalWeightedBlockReciprocalBudget318
open scoped BigOperators

/-- The actual first-axis displacement frequencies are EVEN integers.
Their complete sum is injected into[-4H,4H] without dropping the factor2,
then bounded by the produced complete rational-approximation block budget. -/
theorem actual_even_displacement_frequency_budget (a q H : ℤ) (t N : ℝ)
    (hq : 0<q) (ha : IsCoprime q a)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (hN : 0≤N) :
    (∑ h∈Finset.Icc (-2*H) (2*H), fourierChordCap N (2*h) t)≤
      (((4*H)/rationalBlockLength q-(-4*H)/rationalBlockLength q+1).toNat : ℝ)*
        reciprocalBlockBudget N q := by
  let s := Finset.Icc (-2*H) (2*H)
  have hinj : Set.InjOn (fun h : ℤ => 2*h) (s : Set ℤ) := by
    intro h hh k hk he
    omega
  have hsub : s.image (fun h => 2*h)⊆Finset.Icc (-4*H) (4*H) := by
    intro c hc
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hc
    have hb := Finset.mem_Icc.mp hh
    apply Finset.mem_Icc.mpr
    omega
  calc
    _ = ∑ c∈s.image (fun h => 2*h), fourierChordCap N c t := by
      rw [Finset.sum_image (fun h hh k hk he => hinj hh hk he)]
    _ ≤ ∑ c∈Finset.Icc (-4*H) (4*H), fourierChordCap N c t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc hnot => actual_chord_cap_nonneg N c t hN)
    _ ≤ _ := actual_complete_interval_frequency_budget a q (-4*H) (4*H) t N hq ha ht hN

end ActualOriginalEvenDisplacementFrequencyBudget318
