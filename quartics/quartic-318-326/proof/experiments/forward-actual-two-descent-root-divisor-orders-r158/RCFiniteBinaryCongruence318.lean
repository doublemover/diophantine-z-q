module
public import RCBooleanCommonZero318
public import RCBinaryDigit318
public import RCBooleanDigitPolynomial318
public section
noncomputable section
namespace RCFiniteBinaryCongruence318
open scoped BigOperators
open MvPolynomial RCBooleanDigitPolynomial318

private theorem sum_two_pow (M : ℕ) :
    (∑ j ∈ Finset.range M, 2 ^ j) = 2 ^ M - 1 := by
  have h : (∑ j ∈ Finset.range M, 2 ^ j) + 1 = 2 ^ M := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, pow_succ]; omega
  omega

/-- A nonzero character simultaneously kills all actual low binary digits
of the weighted counts of arbitrary repeated Boolean linear forms. The
degree bounds are proved from the explicit generating coefficients. -/
theorem exists_nonzero_count_congruence (b r M : ℕ)
    (L : Fin r → List (MvPolynomial (Fin b) (ZMod 2)))
    (hdegree : ∀ i Q, Q ∈ L i → Q.totalDegree ≤ 1)
    (hzero : ∀ i Q, Q ∈ L i → eval (0 : Fin b → ZMod 2) Q = 0)
    (hsize : r * (2 ^ M - 1) < b) :
    ∃ x : Fin b → ZMod 2, x ≠ 0 ∧ ∀ i, 2 ^ M ∣ activeCount x (L i) := by
  let P : (Fin r × Fin M) → MvPolynomial (Fin b) (ZMod 2) :=
    fun ij => coefficient (L ij.1) (2 ^ ij.2.val)
  have hPzero : ∀ ij, eval (0 : Fin b → ZMod 2) (P ij) = 0 := by
    intro ij
    dsimp [P]
    rw [eval_coefficient, activeCount_zero _ (hzero ij.1)]
    simp [Nat.choose_eq_zero_of_lt (by positivity : 0 < 2 ^ ij.2.val)]
  have hPdegree : (∑ ij, (P ij).totalDegree) < b := by
    apply lt_of_le_of_lt _ hsize
    calc
      (∑ ij, (P ij).totalDegree) ≤ ∑ ij : Fin r × Fin M, 2 ^ ij.2.val := by
        apply Finset.sum_le_sum
        intro ij _
        exact coefficient_degree _ (hdegree ij.1) _
      _ = r * (2 ^ M - 1) := by
        simp only [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Fin.sum_univ_eq_sum_range, sum_two_pow]
        simp only [Nat.cast_id]
  obtain ⟨x,hx,hP⟩ := RCBooleanCommonZero318.exists_nonzero_common_zero b P hPzero hPdegree
  refine ⟨x,hx,fun i => ?_⟩
  apply RCBinaryDigit318.pow_two_dvd_of_choose_zero
  intro j hj
  have h := hP (i,⟨j,hj⟩)
  simpa only [P, eval_coefficient] using h

end RCFiniteBinaryCongruence318
