module
public import ActualOptimalSelbergBound318
public section
noncomputable section
namespace FiniteMobiusCoefficientBound318
open scoped BigOperators
open FiniteBooleanMobius318 FiniteSelbergMinimizer318
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mobius_abs_le_one (a b : ι → Bool) : |mobius a b|≤1 := by
  rw [mobius,Finset.abs_prod]
  calc
    _ ≤ ∏ i : ι,(1:ℝ) := by
      apply Finset.prod_le_prod
      · intro i _;exact abs_nonneg _
      · intro i _
        cases a i <;> cases b i <;> norm_num [mobiusEntry]
    _ = 1 := by simp
lemma sign_abs (a : ι → Bool) : |sign a|=1 := by
  have h := sign_sq a
  nlinarith [sq_abs (sign a),abs_nonneg (sign a)]

/-- The exact finite inverse has norm at most one after dividing by
its SAME positive truncated mass. No analytic cancellation is assumed. -/
lemma inverse_target_abs_le_one (g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (hg : ∀ b,0≤g b) (hM : 0<mass g cut) (a : ι → Bool) :
    |inverseTransform (target g cut) a|≤1 := by
  have ht (b : ι → Bool) : |target g cut b|=(if cut b then g b else 0)/mass g cut := by
    unfold target
    by_cases hb : cut b
    · rw [if_pos hb,if_pos hb,abs_div,abs_mul,sign_abs,abs_of_nonneg (hg b),abs_of_pos hM,one_mul]
    · simp only [if_neg hb,abs_zero,zero_div]
  calc
    _ ≤ ∑ b : ι → Bool,|mobius a b*target g cut b| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : ι → Bool,|target g cut b| := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (mobius_abs_le_one a b) (abs_nonneg _)).trans_eq (one_mul _)
    _ = 1 := by
      simp_rw [ht]
      rw [←Finset.sum_div]
      exact div_self hM.ne'

lemma actual_coefficient_abs (ν g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (hν : ∀ b,0<ν b) (hg : ∀ b,0≤g b) (hM : 0<mass g cut)
    (a : ι → Bool) : |coefficient ν g cut a|≤1/ν a := by
  rw [coefficient,abs_div,abs_of_pos (hν a)]
  exact div_le_div_of_nonneg_right (inverse_target_abs_le_one g cut hg hM a) (hν a).le

end FiniteMobiusCoefficientBound318
