module
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Tactic
public section
noncomputable section
open scoped BigOperators
namespace PolynomialEvenSquare318
open Polynomial UniqueFactorizationMonoid
variable {F : Type*} [Field F]

/-- Every irreducible polynomial is tested, not only rational linear factors. -/
theorem square_times_unit (a : F[X]) (ha : a ≠ 0)
    (he : ∀ q : F[X], Prime q → Even (multiplicity q a)) :
    ∃ (r : F[X]) (u : F[X]ˣ), r ^ 2 * (u : F[X]) = a := by
  classical
  letI : StrongNormalizationMonoid F[X] :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := normalizedFactors a
  have hc : ∀ q ∈ s, Even (s.count q) := by
    intro q hq
    have hp := prime_of_normalized_factor q hq
    have hh := he q hp
    rw [multiplicity_eq_count_normalizedFactors hp.irreducible ha,
      normalize_normalized_factor q hq] at hh
    exact hh
  let r : F[X] := ∏ q ∈ s.toFinset, q ^ (s.count q / 2)
  have hr : r ^ 2 = s.prod := by
    dsimp only [r]
    have hp : (∏ q ∈ s.toFinset, q ^ (s.count q / 2)) ^ 2 =
        ∏ q ∈ s.toFinset, q ^ s.count q := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro q hq
      rw [← pow_mul]
      congr 1
      obtain ⟨n, hn⟩ := hc q (Multiset.mem_toFinset.mp hq)
      omega
    have hh : (∏ q ∈ s.toFinset, q ^ s.count q) = s.prod := by
      calc
        _ = (∑ q ∈ s.toFinset, s.count q • ({q} : Multiset F[X])).prod := by
          simp only [Multiset.prod_sum, Multiset.prod_nsmul, Multiset.prod_singleton]
        _ = s.prod := by rw [Multiset.toFinset_sum_count_nsmul_eq]
    exact hp.trans hh
  obtain ⟨u, hu⟩ := prod_normalizedFactors ha
  exact ⟨r, u, by rw [hr]; exact hu⟩

/-- Polynomial units over the original field give a nonzero scalar, without
extending that field or choosing an algebraic-closure square root. -/
theorem scalar_square (a : F[X]) (ha : a ≠ 0)
    (he : ∀ q : F[X], Prime q → Even (multiplicity q a)) :
    ∃ (c : F) (r : F[X]), c ≠ 0 ∧ a = C c * r ^ 2 := by
  obtain ⟨r, u, hu⟩ := square_times_unit a ha he
  have hd : (u : F[X]).degree ≤ 0 := (degree_eq_zero_of_isUnit u.isUnit).le
  have hc : (u : F[X]) = C ((u : F[X]).coeff 0) := eq_C_of_degree_le_zero hd
  have hn : (u : F[X]).coeff 0 ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hc, h, map_zero]
  refine ⟨_, r, hn, ?_⟩
  calc
    a = r ^ 2 * (u : F[X]) := hu.symm
    _ = r ^ 2 * C ((u : F[X]).coeff 0) := congrArg (fun z : F[X] => r ^ 2 * z) hc
    _ = C ((u : F[X]).coeff 0) * r ^ 2 := mul_comm _ _
end PolynomialEvenSquare318
