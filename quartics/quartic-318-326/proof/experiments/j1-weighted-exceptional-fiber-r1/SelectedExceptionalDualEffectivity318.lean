module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public section
noncomputable section
open scoped BigOperators

namespace SelectedExceptionalDualEffectivity318

variable {ι : Type*} [Fintype ι]

/-- The actual exceptional intersection quadratic expression. The
index set is exactly the exceptional curves above the chosen open. -/
@[expose] def pairing (Q : ι → ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, v i * (∑ j, Q i j * v j)

/-- Negativity forces an effective exceptional part of a divisor once
its nonexceptional part is effective and its total intersections have
the specified sign. No Cartier divisor downstairs is required. -/
theorem coefficient_nonneg
    (Q : ι → ι → ℝ) (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (negative : ∀ v : ι → ℝ, v ≠ 0 → pairing Q v < 0)
    (a rest : ι → ℝ) (rest_nonneg : ∀ i, 0 ≤ rest i)
    (total_nonpos : ∀ i, (∑ j, Q i j * a j) + rest i ≤ 0) :
    ∀ i, 0 ≤ a i := by
  classical
  let n : ι → ℝ := fun i => max 0 (-a i)
  have hn (i : ι) : 0 ≤ n i := le_max_left _ _
  have hboth (i : ι) : 0 ≤ a i + n i := by
    have hi : -a i ≤ n i := le_max_right _ _
    linarith
  have hrow (i : ι) (hi : n i ≠ 0) : 0 ≤ ∑ j, Q i j * n j := by
    have ha : a i < 0 :=
      lt_of_not_ge (fun han => hi (max_eq_left (neg_nonpos.mpr han)))
    have hz : a i + n i = 0 := by
      have hn' : n i = -a i := max_eq_right (neg_nonneg.mpr ha.le)
      rw [hn',add_neg_cancel]
    have hs : 0 ≤ ∑ j, Q i j * (a j + n j) := by
      apply Finset.sum_nonneg
      intro j _
      by_cases h : i = j
      · subst j
        rw [hz,mul_zero]
      · exact mul_nonneg (offDiag i j h) (hboth j)
    simp only [mul_add,Finset.sum_add_distrib] at hs
    linarith only [hs,rest_nonneg i,total_nonpos i]
  have hnn : 0 ≤ pairing Q n := by
    unfold pairing
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : n i = 0
    · rw [hi,zero_mul]
    · exact mul_nonneg (hn i) (hrow i hi)
  have hzero : n = 0 := by
    by_contra h
    exact (not_lt_of_ge hnn) (negative n h)
  intro i
  have hi : -a i ≤ n i := le_max_right _ _
  have hi0 : n i = 0 := congrFun hzero i
  linarith

/-- Apply the exact abstract intersection rows to the divisor of the
same rational section M/dj in the actual invertible relative dual.
The input canonical row is G⋅E_i = −K_Z⋅E_i. -/
theorem exceptional_order_le
    (Q : ι → ι → ℝ) (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (negative : ∀ v : ι → ℝ, v ≠ 0 → pairing Q v < 0)
    (constantOrder differentialOrder rest canonicalDegree : ι → ℝ)
    (rest_nonneg : ∀ i, 0 ≤ rest i)
    (canonical_nef : ∀ i, 0 ≤ canonicalDegree i)
    (canonical_row : ∀ i,
      (∑ j, Q i j * (constantOrder j - differentialOrder j)) + rest i =
        -canonicalDegree i) :
    ∀ i, differentialOrder i ≤ constantOrder i := by
  have hc (i : ι) :
      (∑ j, Q i j * (constantOrder j - differentialOrder j)) + rest i ≤ 0 :=
    (canonical_row i).trans_le (neg_nonpos.mpr (canonical_nef i))
  intro i
  exact sub_nonneg.mp
    (coefficient_nonneg Q offDiag negative
      (fun j => constantOrder j - differentialOrder j) rest rest_nonneg hc i)

end SelectedExceptionalDualEffectivity318

#print axioms SelectedExceptionalDualEffectivity318.coefficient_nonneg
#print axioms SelectedExceptionalDualEffectivity318.exceptional_order_le
