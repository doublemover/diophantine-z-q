module
public import ActualOriginalFullFiveRationalBound318
public section
noncomputable section
namespace ActualOriginalBinHarmonicBudget318
open ActualOriginalReciprocalBinBudget318 ActualOriginalCompleteFrequencyBudget318
open scoped BigOperators

@[expose] def positiveReciprocalSum (q : ℤ) : ℝ := ∑ b∈Finset.Icc 1 q, (b : ℝ)⁻¹

lemma actual_positive_bin_sum (N : ℝ) (q : ℤ) :
    (∑ b∈Finset.Icc 1 q, binCost N q b)=(q : ℝ)*positiveReciprocalSum q := by
  rw [positiveReciprocalSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hh := Finset.mem_Icc.mp hb
  rw [binCost,if_neg (by omega),if_pos (by omega),div_eq_mul_inv]

lemma actual_negative_bin_sum (N : ℝ) (q : ℤ) (hq : 0<q) :
    (∑ b∈Finset.Icc (-q) (-2), binCost N q b)≤(q : ℝ)*positiveReciprocalSum q := by
  let s := Finset.Icc (-q) (-2)
  have hinj : Set.InjOn (fun b : ℤ => -b-1) (s : Set ℤ) := by
    intro b hb c hc he
    omega
  have hsub : s.image (fun b => -b-1)⊆Finset.Icc 1 q := by
    intro k hk
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
    have hh := Finset.mem_Icc.mp hb
    apply Finset.mem_Icc.mpr
    omega
  calc
    _ = ∑ b∈s, (q : ℝ)/((-b-1 : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hh := Finset.mem_Icc.mp hb
      rw [binCost,if_neg (by omega),if_neg (by omega)]
      simp only [Int.cast_sub,Int.cast_neg,Int.cast_one]
    _ = ∑ k∈s.image (fun b => -b-1), (q : ℝ)/(k : ℝ) := by
      rw [Finset.sum_image (fun b hb c hc he => hinj hb hc he)]
    _ ≤ ∑ k∈Finset.Icc 1 q, (q : ℝ)/(k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro k hk hnot
        have hqi : (0 : ℝ)≤q := by exact_mod_cast (le_of_lt hq)
        have hk' : (0 : ℝ)≤k := by exact_mod_cast (show (0 : ℤ)≤k by have := Finset.mem_Icc.mp hk; omega)
        exact div_nonneg hqi hk')
    _ = _ := by simp only [positiveReciprocalSum,Finset.mul_sum,div_eq_mul_inv]

/-- Both central bins cost N. The full negative tail injects into the
positive harmonic index set; its actual endpoint asymmetry is enlarged,
not dropped. The resulting upper bound is2N+2q*Hq. -/
theorem actual_reciprocal_block_harmonic (N : ℝ) (q : ℤ) (hq : 0<q) :
    reciprocalBlockBudget N q≤2*N+2*(q : ℝ)*positiveReciprocalSum q := by
  have hp : Finset.Icc (-q) q=Finset.Icc (-q) (-2) ∪
      (({-1,0} : Finset ℤ) ∪ Finset.Icc 1 q) := by
    ext b
    simp only [Finset.mem_Icc,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  have hd₁ : Disjoint (Finset.Icc (-q) (-2)) (({-1,0} : Finset ℤ) ∪ Finset.Icc 1 q) := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    simp only [Finset.mem_Icc,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hb hc
    omega
  have hd₂ : Disjoint ({-1,0} : Finset ℤ) (Finset.Icc 1 q) := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hb hc
    omega
  have hm : (∑ b∈({-1,0} : Finset ℤ), binCost N q b)=2*N := by
    norm_num [binCost] <;> ring
  rw [reciprocalBlockBudget,hp,Finset.sum_union hd₁,Finset.sum_union hd₂,hm,actual_positive_bin_sum]
  have hn := actual_negative_bin_sum N q hq
  linarith

end ActualOriginalBinHarmonicBudget318
