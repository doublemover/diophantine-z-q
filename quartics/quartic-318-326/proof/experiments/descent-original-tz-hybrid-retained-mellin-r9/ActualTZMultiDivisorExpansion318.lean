module
public import ActualTZOneDivisorExpansion318
public section
noncomputable section
namespace ActualTZMultiDivisorExpansion318
open scoped BigOperators
open ActualTZOneDivisorExpansion318

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Digit (R : ℝ) := ↥(cut R)
abbrev Assignment (I : Type*) (R : ℝ) := I→Digit R

def amplitude (R : ℝ) (χ : ℝ→ℝ) (d e : Assignment I R) : ℝ :=
  (∏ i : I,coeff R χ (d i).val)*(∏ i : I,coeff R χ (e i).val)

private theorem typed_double (α R : ℝ) (χ : ℝ→ℝ) (p : ℕ)
    (hp : 0<p) (hR : 1<R) (hχ : ∀ t>1,χ t=0) :
    weightedSquare α R χ p=α*Real.log R*∑ d : Digit R,∑ e : Digit R,
      if d.val.lcm e.val∣p then coeff R χ d.val*coeff R χ e.val else 0 := by
  rw [double_squarefree α R χ p hp hR hχ]
  congr 1
  let g (d e : ℕ) : ℝ :=
    if d.lcm e∣p then coeff R χ d*coeff R χ e else 0
  change (∑ d∈cut R,∑ e∈cut R,g d e)=∑ d : Digit R,∑ e : Digit R,g d.val e.val
  calc
    _ = ∑ d : Digit R,∑ e∈cut R,g d.val e :=
      (Finset.sum_coe_sort (cut R) (fun d=>∑ e∈cut R,g d e)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      exact (Finset.sum_coe_sort (cut R) (g d.val)).symm

private theorem condition_factor (R : ℝ) (χ : ℝ→ℝ) (p : I→ℕ) (d e : Assignment I R) :
    (∏ i : I,if (d i).val.lcm (e i).val∣p i then coeff R χ (d i).val*coeff R χ (e i).val else 0) =
      if ∀ i,(d i).val.lcm (e i).val∣p i then amplitude R χ d e else 0 := by
  classical
  by_cases h : ∀ i,(d i).val.lcm (e i).val∣p i
  · rw [if_pos h,amplitude,←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact if_pos (h i)
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Exact product of actual ordinary squarecut weights. Each of the
two assignments runs independently over one squarefree divisor per
position. No equality of prime positions, Gaussian choices, or new
cutoff is introduced. -/
theorem product_expand (α R : ℝ) (χ : ℝ→ℝ) (p : I→ℕ)
    (hp : ∀ i,0<p i) (hR : 1<R) (hχ : ∀ t>1,χ t=0) :
    (∏ i : I,weightedSquare α R χ (p i)) =
      (α*Real.log R)^Fintype.card I*
        ∑ d : Assignment I R,∑ e : Assignment I R,
        if ∀ i,(d i).val.lcm (e i).val∣p i then amplitude R χ d e else 0 := by
  classical
  let f (i : I) (d e : Digit R) :=
    if d.val.lcm e.val∣p i then coeff R χ d.val*coeff R χ e.val else 0
  calc
    _ = ∏ i : I,α*Real.log R*(∑ d : Digit R,∑ e : Digit R,f i d e) := by
      apply Finset.prod_congr rfl
      intro i _
      exact typed_double α R χ (p i) (hp i) hR hχ
    _ = (α*Real.log R)^Fintype.card I*(∏ i : I,∑ d : Digit R,∑ e : Digit R,f i d e) := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_pow]
    _ = _ := by
      congr 1
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact condition_factor R χ p d e

theorem amplitude_bound (R : ℝ) (χ : ℝ→ℝ) (C : ℝ) (hχ : ∀ t,|χ t| ≤ C)
    (d e : Assignment I R) :
    |amplitude R χ d e| ≤ C^(2*Fintype.card I) := by
  have hC : 0≤C := (abs_nonneg _).trans (hχ 0)
  have H (u : Assignment I R) : |∏ i : I,coeff R χ (u i).val| ≤ C^Fintype.card I := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : I,C := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => cutoff_norm R χ _ (u i).property C hχ)
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ]
  rw [amplitude,abs_mul,mul_comm 2 (Fintype.card I),pow_mul,pow_two]
  exact mul_le_mul (H d) (H e) (abs_nonneg _) (pow_nonneg hC _)

end ActualTZMultiDivisorExpansion318
