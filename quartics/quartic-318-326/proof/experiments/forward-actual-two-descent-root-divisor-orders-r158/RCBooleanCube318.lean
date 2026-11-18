module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Sums of polynomials over the Boolean cube `(ZMod 2)^n`

For `p : MvPolynomial (Fin n) (ZMod 2)` of total degree at most `n`, the sum of the
evaluations of `p` over the whole cube `Fin n → ZMod 2` equals the coefficient of the
all-ones monomial `∏ i, X i` (exponent `∑ i, Finsupp.single i 1`).  Consequences: the sum
vanishes when the total degree is `< n`, and if the ordinary product `p * q` (no Boolean
reduction) has all-ones coefficient `1` and `p.totalDegree + q.totalDegree ≤ n`, then some
point of the cube makes both `p` and `q` evaluate to `1`.

Proof idea: a monomial `∏ i, x i ^ d i` sums over the cube to `∏ i, ∑ t : ZMod 2, t ^ d i`;
the factor is `1 + 1 = 0` when `d i = 0` and `0 + 1 = 1` otherwise.  Under the degree
bound `∑ i, d i ≤ n`, the only exponent with every `d i ≥ 1` is the all-ones exponent.
For `n = 0` the cube has one point and the all-ones exponent is the empty sum `0`; the
argument is uniform in `n` and needs no case split.

Note on spelling: in the pinned Mathlib, `MvPolynomial σ R` is an abbreviation of the
one-field structure `AddMonoidAlgebra R (σ →₀ ℕ)`, and the coefficient of the monomial `m`
in `p` is `p.coeff m` (that is, `AddMonoidAlgebra.coeff p m`); the former function
`MvPolynomial.coeff m p` no longer exists.
-/

open scoped BigOperators

public section

namespace ZInQ.BooleanCube

open MvPolynomial

/-- The power sums of the two-element field: `∑ t, t ^ 0 = 0` and `∑ t, t ^ (k + 1) = 1`. -/
private theorem sum_zmod_two_pow (k : ℕ) :
    (∑ t : ZMod 2, t ^ k) = if k = 0 then 0 else 1 := by
  rcases k with _ | k
  · decide
  · have hpow : ∀ t : ZMod 2, t ^ (k + 1) = t := by
      intro t
      have h01 : t = 0 ∨ t = 1 := by revert t; decide
      rcases h01 with rfl | rfl
      · exact zero_pow (Nat.succ_ne_zero k)
      · exact one_pow _
    simp only [hpow]
    rw [ite_eq_right (by omega : ¬(k + 1 = 0))]
    decide

/-- The all-ones exponent takes the value `1` at every variable. -/
private theorem ones_apply (n : ℕ) (j : Fin n) :
    (∑ i : Fin n, Finsupp.single i (1 : ℕ)) j = 1 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- Over `ZMod 2`, if `p` has total degree at most `n`, the sum of `p` over the cube
`Fin n → ZMod 2` is the coefficient of the all-ones monomial in `p`. -/
theorem sum_eval_eq_top_coeff (n : Nat)
    (p : MvPolynomial (Fin n) (ZMod 2))
    (hp : p.totalDegree <= n) :
    (∑ x : (Fin n → ZMod 2), MvPolynomial.eval x p) =
      p.coeff (∑ i : Fin n, Finsupp.single i 1) := by
  classical
  set one : Fin n →₀ ℕ := ∑ i : Fin n, Finsupp.single i 1
  have hone : ∀ j, one j = 1 := fun j => ones_apply n j
  -- the sum of a single monomial over the cube
  have key : ∀ d ∈ p.support,
      (∏ i : Fin n, (∑ t : ZMod 2, t ^ d i)) = if d = one then 1 else 0 := by
    intro d hd
    by_cases h : ∃ i, d i = 0
    · -- some variable is absent: the factor for that variable is `1 + 1 = 0`
      obtain ⟨i, hi⟩ := h
      have hdone : d ≠ one := by
        intro hd'
        have := hone i
        rw [← hd', hi] at this
        omega
      rw [ite_eq_right hdone]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [sum_zmod_two_pow, ite_eq_left hi]
    · -- every variable is present: by the degree bound, `d` is the all-ones exponent
      have h' : ∀ i, d i ≠ 0 := fun i hi => h ⟨i, hi⟩
      have hdeg : (∑ i : Fin n, d i) ≤ n := by
        have h1 := le_totalDegree hd
        have h2 : (d.sum fun _ e => e) = ∑ i : Fin n, d i :=
          Finsupp.sum_fintype _ _ (fun _ => rfl)
        omega
      have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℕ) ≤ d i :=
        fun i _ => Nat.one_le_iff_ne_zero.mpr (h' i)
      have hsum : (∑ i : Fin n, (1 : ℕ)) = ∑ i : Fin n, d i := by
        apply le_antisymm (Finset.sum_le_sum hle)
        simpa using hdeg
      have hd1 : ∀ i, d i = 1 := fun i =>
        ((Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)).symm
      have hdone : d = one := by
        ext i
        rw [hd1 i, hone i]
      rw [ite_eq_left hdone]
      apply Finset.prod_eq_one
      intro i _
      rw [sum_zmod_two_pow, ite_eq_right (h' i)]
  calc (∑ x : Fin n → ZMod 2, eval x p)
      = ∑ x : Fin n → ZMod 2, ∑ d ∈ p.support, p.coeff d * ∏ i, x i ^ d i := by
        simp only [eval_eq']
    _ = ∑ d ∈ p.support, ∑ x : Fin n → ZMod 2, p.coeff d * ∏ i, x i ^ d i :=
        Finset.sum_comm
    _ = ∑ d ∈ p.support, p.coeff d * ∏ i : Fin n, (∑ t : ZMod 2, t ^ d i) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.mul_sum, Fintype.prod_sum]
    _ = ∑ d ∈ p.support, if d = one then p.coeff d else 0 := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [key d hd]
        split_ifs <;> simp
    _ = p.coeff one := by
        rw [Finset.sum_ite_eq']
        split_ifs with h
        · rfl
        · exact (notMem_support_iff.mp h).symm

/-- Over `ZMod 2`, a polynomial in `n` variables of total degree `< n` sums to zero over the
cube `Fin n → ZMod 2` (its all-ones coefficient vanishes for degree reasons). -/
theorem sum_eval_eq_zero_of_totalDegree_lt (n : Nat)
    (p : MvPolynomial (Fin n) (ZMod 2))
    (hp : p.totalDegree < n) :
    (∑ x : (Fin n → ZMod 2), MvPolynomial.eval x p) = 0 := by
  rw [sum_eval_eq_top_coeff n p hp.le]
  apply coeff_eq_zero_of_totalDegree_lt
  have h1 : (∑ i ∈ (∑ i : Fin n, Finsupp.single i (1 : ℕ)).support,
      (∑ i : Fin n, Finsupp.single i (1 : ℕ)) i) =
      ∑ i : Fin n, (∑ i : Fin n, Finsupp.single i (1 : ℕ)) i :=
    Finsupp.sum_fintype _ (fun _ e => e) (fun _ => rfl)
  rw [h1]
  simp only [ones_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]
  exact hp

/-- If the ordinary product `p * q` over `ZMod 2` (read before any Boolean reduction) has
all-ones coefficient `1` and `p.totalDegree + q.totalDegree ≤ n`, then some point of the
cube makes both `p` and `q` evaluate to `1`. -/
theorem exists_simultaneous_one (n : Nat)
    (p q : MvPolynomial (Fin n) (ZMod 2))
    (hdeg : p.totalDegree + q.totalDegree <= n)
    (hcoeff : (p * q).coeff (∑ i : Fin n, Finsupp.single i 1) = 1) :
    ∃ x : Fin n → ZMod 2,
      MvPolynomial.eval x p = 1 ∧ MvPolynomial.eval x q = 1 := by
  have hpq : (p * q).totalDegree ≤ n := (totalDegree_mul p q).trans hdeg
  have hsum := sum_eval_eq_top_coeff n (p * q) hpq
  rw [hcoeff] at hsum
  have hne : (∑ x : Fin n → ZMod 2, eval x (p * q)) ≠ 0 := by
    rw [hsum]
    decide
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨x, ?_⟩
  rw [map_mul] at hx
  have key : ∀ a b : ZMod 2, a * b ≠ 0 → a = 1 ∧ b = 1 := by decide
  exact key _ _ hx

end ZInQ.BooleanCube
