module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace RCBooleanDigitPolynomial318
open MvPolynomial

/-- Coefficient k of the literal generating product ∏ L∈Ls, (1+Y*L).
The recursion avoids an opaque existence assertion for bit polynomials. -/
def coefficient {b : ℕ} : List (MvPolynomial (Fin b) (ZMod 2)) →
    ℕ → MvPolynomial (Fin b) (ZMod 2)
  | [], 0 => 1
  | [], _ + 1 => 0
  | L :: Ls, 0 => coefficient Ls 0
  | L :: Ls, k + 1 => coefficient Ls (k + 1) + L * coefficient Ls k

/-- Number of active Boolean linear forms, counted with repetitions. Repeated
copies encode arbitrary nonnegative integer weights. -/
def activeCount {b : ℕ} (x : Fin b → ZMod 2) :
    List (MvPolynomial (Fin b) (ZMod 2)) → ℕ
  | [] => 0
  | L :: Ls => (eval x L).val + activeCount x Ls

theorem coefficient_zero {b : ℕ} (Ls : List (MvPolynomial (Fin b) (ZMod 2))) :
    coefficient Ls 0 = 1 := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih => exact ih

theorem coefficient_degree {b : ℕ} (Ls : List (MvPolynomial (Fin b) (ZMod 2)))
    (hL : ∀ L ∈ Ls, L.totalDegree ≤ 1) (k : ℕ) :
    (coefficient Ls k).totalDegree ≤ k := by
  induction Ls generalizing k with
  | nil => cases k <;> simp [coefficient]
  | cons L Ls ih =>
      have hhead : L.totalDegree ≤ 1 := hL L (by simp)
      have htail : ∀ Q ∈ Ls, Q.totalDegree ≤ 1 := by
        intro Q hQ
        exact hL Q (by simp [hQ])
      cases k with
      | zero => simp [coefficient_zero]
      | succ k =>
          change (coefficient Ls (k + 1) + L * coefficient Ls k).totalDegree ≤ k + 1
          apply (totalDegree_add _ _).trans
          apply max_le
          · exact ih htail (k + 1)
          · exact (totalDegree_mul _ _).trans
              (by have h := ih htail k; omega)

/-- Evaluation of the explicit coefficient is the actual binomial digit
expression for the integer count, not merely a Boolean-equivalent surrogate. -/
theorem eval_coefficient {b : ℕ}
    (Ls : List (MvPolynomial (Fin b) (ZMod 2))) (x : Fin b → ZMod 2) (k : ℕ) :
    eval x (coefficient Ls k) = ((activeCount x Ls).choose k : ℕ) := by
  induction Ls generalizing k with
  | nil => cases k <;> simp [coefficient, activeCount]
  | cons L Ls ih =>
      cases k with
      | zero => simp [coefficient_zero]
      | succ k =>
          have cases_two : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
          rcases cases_two (eval x L) with hz | ho
          · simp [coefficient, activeCount, hz, ih]
          · have hval : (1 : ZMod 2).val = 1 := by decide
            simp [coefficient, activeCount, ho, hval, ih, Nat.add_comm,
              Nat.choose_succ_succ, Nat.cast_add, add_comm]
            rw [Nat.one_add, Nat.choose_succ_succ, Nat.cast_add]

theorem activeCount_zero {b : ℕ}
    (Ls : List (MvPolynomial (Fin b) (ZMod 2)))
    (hL : ∀ L ∈ Ls, eval (0 : Fin b → ZMod 2) L = 0) :
    activeCount (0 : Fin b → ZMod 2) Ls = 0 := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
      have hhead := hL L (by simp)
      have htail : ∀ Q ∈ Ls, eval (0 : Fin b → ZMod 2) Q = 0 := by
        intro Q hQ
        exact hL Q (by simp [hQ])
      simp only [activeCount, hhead, ih htail, ZMod.val_zero, zero_add]

end RCBooleanDigitPolynomial318
