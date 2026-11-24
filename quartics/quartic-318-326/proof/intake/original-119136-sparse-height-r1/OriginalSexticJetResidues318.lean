module
public import Mathlib.Tactic

/-! Finite algebra for one literal six-branch chart, before any moduli or
Serre duality comparison. The common labelled roots are not reselected by
the interpolation procedure. -/
public section
noncomputable section

namespace OriginalSexticJetResidues318

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

@[expose] def tail (r : Fin 6 → K) (i : Fin 6) : K[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (r j))

@[expose] def split (a : K) (r : Fin 6 → K) : K[X] :=
  C a * ∏ j, (X - C (r j))

theorem split_factor (a : K) (r : Fin 6 → K) (i : Fin 6) :
    split a r = C a * ((X - C (r i)) * tail r i) := by
  unfold split tail
  exact congrArg (C a * ·) ((Finset.mul_prod_erase Finset.univ
    (fun j : Fin 6 => X - C (r j)) (Finset.mem_univ i)).symm)

theorem split_eval (a : K) (r : Fin 6 → K) (i : Fin 6) :
    (split a r).eval (r i) = 0 := by
  rw [split_factor a r i]
  simp

theorem derivative_eval (a : K) (r : Fin 6 → K) (i : Fin 6) :
    (split a r).derivative.eval (r i) = a * (tail r i).eval (r i) := by
  rw [split_factor a r i, derivative_mul, derivative_mul]
  simp

theorem tail_eval_ne (r : Fin 6 → K) (hr : Function.Injective r) (i : Fin 6) :
    (tail r i).eval (r i) ≠ 0 := by
  rw [tail, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simpa only [eval_sub, eval_X, eval_C] using
    (sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 ((hr h).symm)))

theorem derivative_eval_ne (a : K) (ha : a ≠ 0) (r : Fin 6 → K)
    (hr : Function.Injective r) (i : Fin 6) :
    (split a r).derivative.eval (r i) ≠ 0 := by
  rw [derivative_eval]
  exact mul_ne_zero ha (tail_eval_ne r hr i)

private theorem tail_eval_other (r : Fin 6 → K) {i j : Fin 6} (h : i ≠ j) :
    (tail r i).eval (r j) = 0 := by
  rw [tail, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ _⟩)
    (by simp)

private theorem tail_degree (r : Fin 6 → K) (i : Fin 6) :
    (tail r i).natDegree = 5 := by
  rw [tail, natDegree_prod _ _ (fun j _ => X_sub_C_ne_zero (r j))]
  simp [Finset.card_erase_of_mem (Finset.mem_univ i)]

private theorem tail_coeff (r : Fin 6 → K) (i : Fin 6) : (tail r i).coeff 5 = 1 := by
  rw [← tail_degree r i, coeff_natDegree, tail, leadingCoeff_prod]
  simp [leadingCoeff_X_sub_C]

/-- Five is the literal clipping degree, and six *distinct* labels matter.
A duplicate label is not accepted as another zero. -/
theorem eq_of_eval_eq (r : Fin 6 → K) (hr : Function.Injective r) {p q : K[X]}
    (hp : p.natDegree ≤ 5) (hq : q.natDegree ≤ 5) (eq : ∀ i, p.eval (r i) = q.eval (r i)) :
    p = q := by
  classical
  by_contra hn
  have nz : p - q ≠ 0 := sub_ne_zero.mpr hn
  have hcard : 6 ≤ (p - q).roots.toFinset.card := by
    let s := (Finset.univ : Finset (Fin 6)).map ⟨r, hr⟩
    have hsub : s ⊆ (p-q).roots.toFinset := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      have hz : (p-q).eval (r i) = 0 := by rw [eval_sub, eq i, sub_self]
      exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (IsRoot.def.mpr hz))
    have hc := Finset.card_le_card hsub
    simpa only [s, Finset.card_map, Finset.card_univ, Fintype.card_fin] using hc
  have hd : (p-q).natDegree ≤ 5 := (natDegree_sub_le p q).trans (max_le hp hq)
  exact (by decide : ¬ (6:ℕ) ≤ 5)
    (hcard.trans ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hd)))

/-- Lagrange leading-coefficient functional for the actual six roots.
The leading factor a can be nonmonic and must not be dropped. -/
theorem coeff_eq_sum (a : K) (r : Fin 6 → K) (hr : Function.Injective r)
    (p : K[X]) (hp : p.natDegree ≤ 5) :
    p.coeff 5 / a = ∑ i, p.eval (r i) / (split a r).derivative.eval (r i) := by
  let c (i : Fin 6) : K := p.eval (r i) / (tail r i).eval (r i)
  let q := ∑ i, C (c i) * tail r i
  have hq : q.natDegree ≤ 5 := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le ..).trans_eq (tail_degree r i)
  have he (i : Fin 6) : p.eval (r i) = q.eval (r i) := by
    unfold q
    rw [eval_finsetSum, Finset.sum_eq_single i]
    · rw [eval_mul, eval_C]
      exact (div_mul_cancel₀ _ (tail_eval_ne r hr i)).symm
    · intro j _ hj
      rw [eval_mul, tail_eval_other r hj, mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_univ _))
  have pp : p = q := eq_of_eval_eq r hr hp hq he
  rw [pp]
  have coeff : q.coeff 5 = ∑ i, c i := by
    unfold q
    simp only [finsetSum_coeff, coeff_C_mul, tail_coeff, mul_one]
  rw [coeff, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_eval, ← pp]
  dsimp [c]
  rw [div_div, mul_comm ((tail r i).eval (r i)) a]

/-- First-order branch displacement is uniquely determined, in the same
ordinary base direction, by the derivative of the defining equation.
This is the coefficient of ε after linearization, not a choice of lift. -/
theorem branch_velocity_iff (a : K) (ha : a ≠ 0)
    (r : Fin 6 → K) (hr : Function.Injective r) (G : K[X]) (i : Fin 6) (v : K) :
    G.eval (r i) + (split a r).derivative.eval (r i) * v = 0 ↔
      v = -G.eval (r i) / (split a r).derivative.eval (r i) := by
  have hn := derivative_eval_ne a ha r hr i
  rw [eq_div_iff hn]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end OriginalSexticJetResidues318

#print axioms OriginalSexticJetResidues318.coeff_eq_sum
#print axioms OriginalSexticJetResidues318.branch_velocity_iff
