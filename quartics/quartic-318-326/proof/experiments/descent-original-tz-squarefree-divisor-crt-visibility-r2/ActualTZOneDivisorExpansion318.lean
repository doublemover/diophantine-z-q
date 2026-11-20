module
public import Mathlib
public section
noncomputable section
namespace ActualTZOneDivisorExpansion318
open scoped BigOperators ArithmeticFunction.Moebius

/-- Exact floor cutoff includes the endpoint d=R when R is integral. -/
def cut (R : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊R⌋₊).filter Squarefree

def coeff (R : ℝ) (χ : ℝ→ℝ) (d : ℕ) : ℝ :=
  ((μ d:ℤ):ℝ)*χ (Real.log (d:ℝ)/Real.log R)

/-- Same formula as the literal ordinary majorant (36). The selected
prime-ray input is irrelevant for this expansion. -/
def weightedSquare (α R : ℝ) (χ : ℝ→ℝ) (p : ℕ) : ℝ :=
  α*Real.log R*(∑ d∈p.divisors,coeff R χ d)^2

theorem coeff_off_cut (R : ℝ) (χ : ℝ→ℝ) (d : ℕ) (hR : 1<R)
    (hd : 0<d) (hχ : ∀ t>1,χ t=0) (h : d∉cut R) : coeff R χ d=0 := by
  by_cases hs : Squarefree d
  · have hb : ¬d≤⌊R⌋₊ := by
      intro h'
      exact h (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,h'⟩,hs⟩)
    have gt : R<(d:ℝ) := lt_of_not_ge
      (fun h' => hb ((Nat.le_floor_iff (show 0≤R from le_trans zero_le_one hR.le)).mpr h'))
    have hlog := Real.log_lt_log (zero_lt_one.trans hR) gt
    have ht : 1<Real.log (d:ℝ)/Real.log R :=
      (lt_div_iff₀ (Real.log_pos hR)).mpr (by simpa only [one_mul] using hlog)
    simp only [coeff,hχ _ ht,mul_zero]
  · simp [coeff,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

theorem divisor_cut (R : ℝ) (χ : ℝ→ℝ) (p : ℕ) (hp : 0<p)
    (hR : 1<R) (hχ : ∀ t>1,χ t=0) :
    (∑ d∈p.divisors,coeff R χ d)=
      ∑ d∈cut R,if d∣p then coeff R χ d else 0 := by
  classical
  have he : p.divisors.filter (fun d => d∈cut R)=(cut R).filter (fun d => d∣p) := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,hp.ne',and_true]
    tauto
  calc
    _ = ∑ d∈p.divisors,if d∈cut R then coeff R χ d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d∈cut R
      · simp only [if_pos h]
      · have hd' := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hp
        simp only [if_neg h,coeff_off_cut _ _ _ hR hd' hχ h]
    _ = ∑ d∈p.divisors.filter (fun d => d∈cut R),coeff R χ d := by rw [Finset.sum_filter]
    _ = _ := by rw [he,Finset.sum_filter]

theorem double_squarefree (α R : ℝ) (χ : ℝ→ℝ) (p : ℕ) (hp : 0<p)
    (hR : 1<R) (hχ : ∀ t>1,χ t=0) :
    weightedSquare α R χ p=α*Real.log R*
      ∑ d∈cut R,∑ e∈cut R,if d.lcm e∣p then coeff R χ d*coeff R χ e else 0 := by
  classical
  unfold weightedSquare
  rw [divisor_cut R χ p hp hR hχ,pow_two,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Nat.lcm_dvd_iff]
  by_cases hd : d∣p <;> by_cases he : e∣p <;> simp [hd,he]

theorem cut_pos {R : ℝ} {d : ℕ} (hd : d∈cut R) : 0<d :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1

theorem cut_card_le (R : ℝ) : (cut R).card≤⌊R⌋₊+1 := by
  have hs : cut R⊆Finset.range (⌊R⌋₊+1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2)
  exact (Finset.card_le_card hs).trans_eq (Finset.card_range _)

theorem cutoff_norm (R : ℝ) (χ : ℝ→ℝ) (d : ℕ) (hd : d∈cut R) (C : ℝ)
    (hχ : ∀ t,|χ t| ≤ C) : |coeff R χ d| ≤ C := by
  have hs : Squarefree d := (Finset.mem_filter.mp hd).2
  have hμ : |((μ d:ℤ):ℝ)|=1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hs]
    simp only [Int.cast_pow,Int.cast_neg,Int.cast_one,abs_pow,abs_neg,abs_one,one_pow]
  rw [coeff,abs_mul,hμ,one_mul]
  exact hχ _

end ActualTZOneDivisorExpansion318
