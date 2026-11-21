module
public import ActualTZOneDivisorExpansion318
import all ActualTZOneDivisorExpansion318
public section
noncomputable section
namespace ActualTZOrdinaryCutoffEnvelope318
open scoped BigOperators
open ActualTZOneDivisorExpansion318

/-- Exact old squarefree cutoff count bounds the ordinary ν factor;
no divisor subpower theorem or deeper number theory is needed. -/
theorem one_weight_le (α R : ℝ) (χ : ℝ→ℝ) (p : ℕ) (hp : 0<p) (hR : 1<R)
    (hα : 0≤α) (hα' : α≤1) (C : ℝ) (hC : ∀ t,|χ t|≤C)
    (hs : ∀ t>1,χ t=0) :
    |weightedSquare α R χ p|≤Real.log R*(2*R*C)^2 := by
  have hC0 : 0≤C := (abs_nonneg _).trans (hC 0)
  have hL := Real.log_pos hR
  have hR0 : 0≤R := (zero_lt_one.trans hR).le
  have hB : ((cut R).card:ℝ)≤2*R := by
    have hx : ((cut R).card:ℝ)≤(⌊R⌋₊:ℝ)+1 := by exact_mod_cast cut_card_le R
    have hf := Nat.floor_le hR0
    linarith
  let A := ∑ d∈cut R,if d∣p then coeff R χ d else 0
  have hA : |A|≤2*R*C := by
    dsimp only [A]
    calc
      _ ≤ ∑ d∈cut R,|if d∣p then coeff R χ d else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d∈cut R,C := by
        apply Finset.sum_le_sum
        intro d hd
        by_cases h : d∣p
        · simpa only [if_pos h] using cutoff_norm R χ d hd C hC
        · simpa only [if_neg h,abs_zero] using hC0
      _ = ((cut R).card:ℝ)*C := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hB hC0
  have hαL : α*Real.log R≤Real.log R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hα' hL.le
  unfold weightedSquare
  rw [divisor_cut R χ p hp hR hs]
  change |α*Real.log R*A^2|≤_
  rw [abs_mul,abs_mul,abs_of_nonneg hα,abs_of_nonneg hL.le,abs_pow]
  exact mul_le_mul hαL (pow_le_pow_left₀ (abs_nonneg _) hA 2)
    (pow_nonneg (abs_nonneg _) _) hL.le

theorem product_le {I : Type*} [Fintype I] (α R : ℝ) (χ : ℝ→ℝ)
    (p : I→ℕ) (hp : ∀ i,0<p i) (hR : 1<R)
    (hα : 0≤α) (hα' : α≤1) (C : ℝ) (hC : ∀ t,|χ t|≤C)
    (hs : ∀ t>1,χ t=0) :
    |∏ i : I,weightedSquare α R χ (p i)|≤
      (Real.log R*(2*R*C)^2)^Fintype.card I := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : I,Real.log R*(2*R*C)^2 := Finset.prod_le_prod₀
      (fun _ _=>abs_nonneg _) (fun i _=>one_weight_le α R χ (p i) (hp i) hR hα hα' C hC hs)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ]

end ActualTZOrdinaryCutoffEnvelope318
