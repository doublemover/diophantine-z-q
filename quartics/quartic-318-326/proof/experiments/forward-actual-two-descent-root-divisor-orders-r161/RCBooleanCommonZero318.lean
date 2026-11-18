module
public import RCBooleanCube318
public section
noncomputable section
namespace RCBooleanCommonZero318
open scoped BigOperators
open MvPolynomial

/-- Degree bookkeeping for the literal common-zero indicator; no Boolean
reduction of the ordinary polynomial product is used. -/
private lemma indicator_degree {ι : Type*} (s : Finset ι) (b : ℕ)
    (P : ι → MvPolynomial (Fin b) (ZMod 2)) :
    (∏ i ∈ s, (1 + P i)).totalDegree ≤ ∑ i ∈ s, (P i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      have hfactor : (1 + P i).totalDegree ≤ (P i).totalDegree := by
        exact (totalDegree_add _ _).trans (by simp)
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hfactor ih)

/-- The exact characteristic-two common-zero step used in the RC draft's
binary-congruence argument. The existing Boolean-cube parity theorem is
reused; this theorem neither supplies digit polynomials nor asserts an
analytic or global arithmetic consequence. -/
theorem exists_nonzero_common_zero {ι : Type*} [Fintype ι]
    (b : ℕ) (P : ι → MvPolynomial (Fin b) (ZMod 2))
    (hzero : ∀ i, eval (0 : Fin b → ZMod 2) (P i) = 0)
    (hdegree : (∑ i, (P i).totalDegree) < b) :
    ∃ x : Fin b → ZMod 2, x ≠ 0 ∧ ∀ i, eval x (P i) = 0 := by
  classical
  let Q : MvPolynomial (Fin b) (ZMod 2) := ∏ i, (1 + P i)
  have hQdegree : Q.totalDegree < b :=
    lt_of_le_of_lt (indicator_degree Finset.univ b P) hdegree
  have hsum := ZInQ.BooleanCube.sum_eval_eq_zero_of_totalDegree_lt b Q hQdegree
  have hQzero : eval (0 : Fin b → ZMod 2) Q = 1 := by
    simp only [Q, map_prod, map_add, map_one, hzero, add_zero, Finset.prod_const_one]
  by_contra hnone
  have hvanish (x : Fin b → ZMod 2) (hx : x ≠ 0) : eval x Q = 0 := by
    have hex : ∃ i, eval x (P i) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hnone ⟨x,hx,h⟩
    obtain ⟨i,hi⟩ := hex
    have hone : eval x (P i) = 1 := by
      have cases_two : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
      exact (cases_two _).resolve_left hi
    change eval x (∏ i, (1 + P i)) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa only [map_add, map_one, hone] using
      (show (1 : ZMod 2) + 1 = 0 by decide)
  have hsum_one : (∑ x : Fin b → ZMod 2, eval x Q) = 1 := by
    rw [Finset.sum_eq_single (0 : Fin b → ZMod 2)]
    · exact hQzero
    · intro x _ hx
      exact hvanish x hx
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hsum_one] at hsum
  exact (by decide : (1 : ZMod 2) ≠ 0) hsum

end RCBooleanCommonZero318
