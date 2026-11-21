module
public import Mathlib.Tactic
public section
namespace ActualFTTwoFormMinors318

/-- Forms are in the literal (u,q) coordinate order; the removed
contact duplicates have one Option label per slope. -/
@[expose] def coeff (Q : ℤ) : Option ℤ → ℤ × ℤ
  | none => (0,1)
  | some k => (1,k*Q^2)

@[expose] def det (v w : ℤ×ℤ) : ℤ := v.1*w.2-v.2*w.1

theorem det_contacts (Q i j : ℤ) :
    det (coeff Q (some i)) (coeff Q (some j)) = (j-i)*Q^2 := by
  simp only [coeff,det,Prod.fst,Prod.snd]
  ring

theorem nonzero_minor (Q : ℤ) (hq : Q ≠ 0)
    {i j : Option ℤ} (h : i ≠ j) : det (coeff Q i) (coeff Q j) ≠ 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (h rfl).elim
    | some j => norm_num [det,coeff]
  | some i =>
    cases j with
    | none => norm_num [det,coeff]
    | some j =>
      rw [det_contacts]
      have hij : j ≠ i := fun H => h (congrArg some H.symm)
      exact mul_ne_zero (sub_ne_zero.mpr hij) (pow_ne_zero _ hq)

/-- Pairwise nonproportional linear parts over ℚ, as required by
the published finite-complexity criterion. -/
theorem no_proportional (Q : ℤ) (hq : Q ≠ 0)
    {i j : Option ℤ} (h : i ≠ j) (t : ℚ) :
    ¬ (((coeff Q i).1:ℚ) = t*((coeff Q j).1:ℚ) ∧
      ((coeff Q i).2:ℚ) = t*((coeff Q j).2:ℚ)) := by
  intro he
  have H : (det (coeff Q i) (coeff Q j):ℚ) = 0 := by
    simp only [det,Int.cast_sub,Int.cast_mul]
    rw [he.1,he.2]
    ring
  exact nonzero_minor Q hq h (by exact_mod_cast H)

end ActualFTTwoFormMinors318
