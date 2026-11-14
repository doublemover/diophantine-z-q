module
public import ActualOriginalCenteredFrequencyBins318
public section
noncomputable section
namespace ActualOriginalReciprocalBinBudget318
open scoped BigOperators

/-- Resonances cost the full interval length N, not the totalized 1/0. -/
@[expose] def reciprocalCap (N x : ℝ) : ℝ := if x=0 then N else min N (1/(2*|x|))

/-- Two central bins cost N. Every other bin has its explicit harmonic
reciprocal cost. No claim of a logarithmic simplification is hidden here. -/
@[expose] def binCost (N : ℝ) (q b : ℤ) : ℝ :=
  if b= -1 ∨ b=0 then N else if 0<b then (q : ℝ)/(b : ℝ) else (q : ℝ)/(-(b : ℝ)-1)

lemma actual_reciprocal_cap_le (N x : ℝ) : reciprocalCap N x≤N := by
  unfold reciprocalCap
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma actual_bin_cost_nonneg (N : ℝ) (q b : ℤ) (hN : 0≤N) (hq : 0<q) :
    0≤binCost N q b := by
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  unfold binCost
  split_ifs with hb hp
  · exact hN
  · have hb' : (0 : ℝ)<b := by exact_mod_cast hp
    positivity
  · have hb' : (b : ℝ)≤ -2 := by exact_mod_cast (show b≤ -2 by omega)
    exact div_nonneg (le_of_lt hqi) (by linarith)

/-- Each actual centered value is charged to its own literal floor bin,
including both central bins and exact zero. -/
theorem actual_reciprocal_cap_bin_bound (N : ℝ) (q : ℤ) (x : ℝ) (hq : 0<q) :
    reciprocalCap N x≤binCost N q ⌊2*(q : ℝ)*x⌋ := by
  by_cases hz : x=0
  · subst x
    simp [reciprocalCap,binCost]
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  let b : ℤ := ⌊2*(q : ℝ)*x⌋
  change reciprocalCap N x≤binCost N q b
  by_cases hb : b= -1 ∨ b=0
  · rw [binCost,if_pos hb]
    exact actual_reciprocal_cap_le N x
  have hl : (b : ℝ)≤2*(q : ℝ)*x := Int.floor_le _
  have hu : 2*(q : ℝ)*x<(b : ℝ)+1 := Int.lt_floor_add_one _
  rw [reciprocalCap,if_neg hz,binCost,if_neg hb]
  apply (min_le_right _ _).trans
  by_cases hp : 0<b
  · rw [if_pos hp]
    have hb' : (0 : ℝ)<b := by exact_mod_cast hp
    have hx : 0<x := by nlinarith
    rw [abs_of_pos hx]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2*x) hb').mpr
    nlinarith
  · rw [if_neg hp]
    have hb' : (b : ℝ)≤ -2 := by exact_mod_cast (show b≤ -2 by omega)
    have hx : x<0 := by nlinarith
    rw [abs_of_neg hx]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2*(-x)) (by linarith : (0 : ℝ)< -(b : ℝ)-1)).mpr
    nlinarith

/-- Finite injective bin packing sums over EVERY original index and
then over the complete bin interval. No near-resonant index is omitted. -/
theorem actual_finite_reciprocal_bin_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (N : ℝ) (q : ℤ) (hN : 0≤N) (hq : 0<q)
    (hinj : Set.InjOn (fun i => ⌊2*(q : ℝ)*x i⌋) (s : Set ι))
    (hrange : ∀ i∈s, ⌊2*(q : ℝ)*x i⌋∈Finset.Icc (-q) q) :
    (∑ i∈s, reciprocalCap N (x i))≤∑ b∈Finset.Icc (-q) q, binCost N q b := by
  calc
    _ ≤ ∑ i∈s, binCost N q ⌊2*(q : ℝ)*x i⌋ := by
      apply Finset.sum_le_sum
      intro i hi
      exact actual_reciprocal_cap_bin_bound N q (x i) hq
    _ = ∑ b∈s.image (fun i => ⌊2*(q : ℝ)*x i⌋), binCost N q b := by
      rw [Finset.sum_image (fun i hi j hj he => hinj hi hj he)]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
        exact hrange i hi
      · intro b hb hnot
        exact actual_bin_cost_nonneg N q b hN hq

end ActualOriginalReciprocalBinBudget318
