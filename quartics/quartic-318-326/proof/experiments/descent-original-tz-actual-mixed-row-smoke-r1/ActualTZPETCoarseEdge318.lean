module
public import Mathlib
public section
noncomputable section
namespace ActualTZPETCoarseEdge318
open scoped BigOperators

@[expose] def interval (L s : ℕ) (F : ℕ→ℝ) : ℝ :=
  ∑ t∈Finset.range L,F (s+t+1)

@[expose] def mean (L s : ℕ) (F : ℕ→ℝ) : ℝ := interval L s F/(L:ℝ)

/-- The old [1,L] coarse interval is smoothed by a fresh
independent [1,M] fine digit. Neither interval is recentered. -/
@[expose] def smooth (L M : ℕ) (F : ℕ→ℝ) : ℝ := mean M 0 (fun h=>mean L h F)

theorem interval_diff (L h : ℕ) (F : ℕ→ℝ) :
    interval L h F-interval L 0 F=interval h L F-interval h 0 F := by
  let f (i : ℕ) := F (i+1)
  have hh := Finset.sum_range_add f h L
  have hl := Finset.sum_range_add f L h
  rw [Nat.add_comm h L] at hh
  simp only [f,zero_add,interval,add_comm] at hh hl ⊢
  linarith only [hh,hl]

theorem mean_swap (L M : ℕ) (F : ℕ→ℝ) :
    smooth L M F=mean L 0 (fun m=>mean M m F) := by
  have H : (∑ t∈Finset.range M,∑ u∈Finset.range L,F (t+1+u+1))=
      ∑ u∈Finset.range L,∑ t∈Finset.range M,F (u+1+t+1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    omega
  unfold smooth mean interval
  simp only [zero_add,←Finset.sum_div,div_div]
  rw [H,mul_comm (L:ℝ)]

private theorem interval_abs_le (L s : ℕ) (F K : ℕ→ℝ) (hK : ∀ t,|F t|≤K t) :
    |interval L s F|≤interval L s K := by
  unfold interval
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t _=>hK _))

theorem mean_nonneg (L s : ℕ) (F : ℕ→ℝ) (hF : ∀ n,0≤F n) : 0≤mean L s F := by
  unfold mean interval
  exact div_nonneg (Finset.sum_nonneg (fun _ _=>hF _)) (by positivity)

/-- Exact two-edge bound for a fixed fine digit. The two upper
envelope blocks have actual width M and starts 1 and L+1. -/
theorem shift_error (L M h : ℕ) (hh : h≤M) (hL : 0<L) (F K : ℕ→ℝ)
    (hK : ∀ t,|F t|≤K t) :
    |mean L h F-mean L 0 F|≤(interval M 0 K+interval M L K)/(L:ℝ) := by
  have hk (t : ℕ) : 0≤K t := (abs_nonneg _).trans (hK t)
  have H (s : ℕ) : |interval h s F|≤interval M s K := by
    refine (interval_abs_le h s F K hK).trans ?_
    unfold interval
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hh) (fun _ _ _=>hk _)
  unfold mean
  rw [←sub_div,abs_div,abs_of_nonneg (by positivity : (0:ℝ)≤L),interval_diff]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (abs_sub _ _).trans ((add_le_add (H L) (H 0)).trans_eq (add_comm _ _))

theorem smooth_error (L M : ℕ) (hL : 0<L) (hM : 0<M) (F K : ℕ→ℝ)
    (hK : ∀ t,|F t|≤K t) :
    |smooth L M F-mean L 0 F|≤((M:ℝ)/(L:ℝ))*(mean M 0 K+mean M L K) := by
  let A := mean L 0 F
  let B := (interval M 0 K+interval M L K)/(L:ℝ)
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hA : ∑ _∈Finset.range M,A=(M:ℝ)*A := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hh : smooth L M F-A=(∑ t∈Finset.range M,(mean L (t+1) F-A))/(M:ℝ) := by
    change (∑ t∈Finset.range M,mean L (t+1) F)/(M:ℝ)-A=_
    rw [Finset.sum_sub_distrib,hA]
    field_simp [hM'.ne'] <;> ring
  have hL' : (0:ℝ)<L := by exact_mod_cast hL
  calc
    _ = |∑ t∈Finset.range M,(mean L (t+1) F-A)|/(M:ℝ) := by
      change |smooth L M F-A|=_
      rw [hh,abs_div,abs_of_nonneg hM'.le]
    _ ≤ (∑ _t∈Finset.range M,B)/(M:ℝ) := by
      apply div_le_div_of_nonneg_right _ hM'.le
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro t ht
      exact shift_error L M (t+1) (by have h:=Finset.mem_range.mp ht; omega) hL F K hK
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,B,mean]
      field_simp [hM'.ne',hL'.ne'] <;> ring

end ActualTZPETCoarseEdge318
