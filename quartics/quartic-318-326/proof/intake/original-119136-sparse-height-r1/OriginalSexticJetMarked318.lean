module
public import OriginalSexticJetResidues318

/-! Exact ordinary sextic-jet arithmetic over the arithmetic field, checked
against a fixed labelled splitting field. Geometric Čech/Serre comparison is
a separately explicit input; member identities here are computed data. -/
public section
noncomputable section

namespace OriginalSexticJetMarked318

open Polynomial OriginalSexticJetResidues318
open scoped BigOperators

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

/-- Data read from the actual one-germ sextic. F, G, remainders and leading
factor are over the arithmetic field; only the fixed six labels may require
the splitting extension. G is the derivative along the specified ordinary
T, not the derivative with respect to some point's other parameter. -/
structure Certificate (E K : Type*) [Field E] [Field K] [Algebra E K] where
  F : E[X]
  G : E[X]
  true_jet_degree : G.natDegree ≤ 6
  a : E
  leading_nonzero : a ≠ 0
  labels : Fin 6 → K
  distinct : Function.Injective labels
  factorization : F.map (algebraMap E K) = split (algebraMap E K a) labels
  remainder : Fin 3 → E[X]
  small : ∀ i, (remainder i).natDegree ≤ 5
  relation : ∀ i : Fin 3, ∃ Q : E[X], X ^ (i : ℕ) * G - (remainder i) * F.derivative = F * Q

@[expose] def moment (J : Certificate E K) (i : Fin 3) : E :=
  -2 * ((J.remainder i).coeff 5 / J.a)

/-- The raw determinant in the ordinary Hodge wedge dx/y∧x dx/y. A global
Čech orientation changes the sign of the entire matrix, not this output. -/
@[expose] def rawB (J : Certificate E K) : E :=
  moment J 0 * moment J 2 - (moment J 1)^2

@[expose] def branchSlope (J : Certificate E K) (v : Fin 6) : K :=
  (split (algebraMap E K J.a) J.labels).derivative.eval (J.labels v)

theorem branchSlope_ne (J : Certificate E K) (v : Fin 6) : branchSlope J v ≠ 0 := by
  exact derivative_eval_ne _ (by simpa only [map_zero] using (algebraMap E K).injective.ne J.leading_nonzero)
    _ J.distinct _

@[expose] def branchMoment (J : Certificate E K) (i : Fin 3) : K :=
  -2 * ∑ v, (J.labels v)^(i:ℕ) * (J.G.map (algebraMap E K)).eval (J.labels v) /
    (branchSlope J v)^2

private theorem remainder_read (J : Certificate E K) (i : Fin 3) (v : Fin 6) :
    ((J.remainder i).map (algebraMap E K)).eval (J.labels v) =
      (J.labels v)^(i:ℕ) * (J.G.map (algebraMap E K)).eval (J.labels v) /
        branchSlope J v := by
  let σ := algebraMap E K
  obtain ⟨Q, e⟩ := J.relation i
  have h := congrArg (fun p : E[X] => (p.map σ).eval (J.labels v)) e
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    eval_sub, eval_mul, eval_pow, eval_X, ← derivative_map] at h
  rw [J.factorization, split_eval, zero_mul] at h
  apply (eq_div_iff (branchSlope_ne J v)).mpr
  exact (sub_eq_zero.mp h).symm

/-- The determinant computation itself is in E; the divided-difference
labelled root formula checked in K cannot accidentally assign B its own
extension or a different root ordering. -/
theorem moment_eq_branch (J : Certificate E K) (i : Fin 3) :
    algebraMap E K (moment J i) = branchMoment J i := by
  have h := coeff_eq_sum (algebraMap E K J.a) J.labels J.distinct
    ((J.remainder i).map (algebraMap E K))
    (by simpa only [natDegree_map] using J.small i)
  change ((J.remainder i).map (algebraMap E K)).coeff 5 / (algebraMap E K J.a) =
    ∑ v, ((J.remainder i).map (algebraMap E K)).eval (J.labels v) / branchSlope J v at h
  simp only [moment, branchMoment, map_mul, map_neg, map_ofNat, map_div₀]
  rw [← coeff_map, h]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [remainder_read, div_div, pow_two]

theorem rawB_eq_branch (J : Certificate E K) :
    algebraMap E K (rawB J) = branchMoment J 0 * branchMoment J 2 - branchMoment J 1 ^ 2 := by
  simp only [rawB, map_sub, map_mul, map_pow, moment_eq_branch]

/-- Exact signed Čech entries, if established for the actual principally
polarized family with this wedge, identify the arithmetic raw determinant.
The chosen common orientation may be reversed, not independently per row. -/
theorem rawB_of_polarized_entries (J : Certificate E K) (b00 b01 b11 ε : E)
    (orientation : ε ^ 2 = 1)
    (h00 : algebraMap E K b00 = algebraMap E K ε * branchMoment J 0)
    (h01 : algebraMap E K b01 = algebraMap E K ε * branchMoment J 1)
    (h11 : algebraMap E K b11 = algebraMap E K ε * branchMoment J 2) :
    b00 * b11 - b01^2 = rawB J := by
  apply (algebraMap E K).injective
  rw [map_sub, map_mul, map_pow, rawB_eq_branch, h00, h01, h11]
  have h := congrArg (algebraMap E K) orientation
  rw [map_pow, map_one] at h
  calc
    _ = (algebraMap E K ε)^2 *
      (branchMoment J 0 * branchMoment J 2 - branchMoment J 1^2) := by ring
    _ = _ := by rw [h, one_mul]

end OriginalSexticJetMarked318

#print axioms OriginalSexticJetMarked318.rawB_eq_branch
#print axioms OriginalSexticJetMarked318.rawB_of_polarized_entries
