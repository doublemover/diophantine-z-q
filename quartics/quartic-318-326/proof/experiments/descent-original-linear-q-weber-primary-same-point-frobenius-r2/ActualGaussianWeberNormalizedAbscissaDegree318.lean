module
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section

namespace ActualGaussianWeberNormalizedAbscissaDegree318

open Polynomial

variable {k : Type*} [Field k]

/-- Canonical coprime reduction cannot increase either degree.
The zero numerator is handled independently of divisibility. -/
theorem normalize_both_degrees (A B : k[X]) (hB : B ≠ 0) :
    (RatFunc.mk A B).num.natDegree ≤ A.natDegree ∧
      (RatFunc.mk A B).denom.natDegree ≤ B.natDegree := by
  constructor
  · by_cases hA : A = 0
    · subst A
      simp only [RatFunc.mk_eq_div,map_zero,zero_div,RatFunc.num_zero,natDegree_zero,le_refl]
    · apply Polynomial.natDegree_le_of_dvd _ hA
      rw [RatFunc.mk_eq_div]
      exact RatFunc.num_div_dvd A hB
  · apply Polynomial.natDegree_le_of_dvd _ hB
    rw [RatFunc.mk_eq_div]
    exact RatFunc.denom_div_dvd A B

/-- A cap on both unnormalized reductions is a cap on the canonical
coprime pair as well. No choice of an unrelated rational presentation. -/
theorem normalized_max_le {A B : k[X]} (hB : B ≠ 0) (n : ℕ)
    (ha : A.natDegree ≤ n) (hb : B.natDegree ≤ n) :
    max (RatFunc.mk A B).num.natDegree (RatFunc.mk A B).denom.natDegree ≤ n := by
  obtain ⟨hA',hB'⟩ := normalize_both_degrees A B hB
  exact max_le_iff.mpr ⟨hA'.trans ha,hB'.trans hb⟩

/-- The exact stock normalized pair for a quotient inherits the cap,
its denominator is nonzero, and its numerator and denominator are
coprime. This is the consumed post-Gauss normalization interface. -/
theorem normalized_coprime_cap (A B : k[X]) (hB : B ≠ 0) (n : ℕ)
    (ha : A.natDegree ≤ n) (hb : B.natDegree ≤ n) :
    let r := RatFunc.mk A B
    IsCoprime r.num r.denom ∧ r.denom ≠ 0 ∧
      max r.num.natDegree r.denom.natDegree ≤ n :=
  ⟨RatFunc.isCoprime_num_denom (RatFunc.mk A B),
    RatFunc.denom_ne_zero (RatFunc.mk A B),normalized_max_le hB n ha hb⟩

/-- Once both exact normalized coordinates are p-th powers, the
nonconstant max-degree p cap forces the same two roots to be at most
linear, and at least one is linear. No function-field index theorem
or pole claim is assumed in this stock degree step. -/
theorem root_degrees_one_of_nonconstant_cap {A B U W : k[X]} {p : ℕ}
    (hp : 0 < p) (hA : U^p=A) (hB : W^p=B)
    (hne : 0 < max A.natDegree B.natDegree)
    (hcap : max A.natDegree B.natDegree ≤ p) :
    U.natDegree ≤ 1 ∧ W.natDegree ≤ 1 ∧
      (U.natDegree=1 ∨ W.natDegree=1) := by
  have h₁ : p * U.natDegree ≤ p := by
    have h := (le_max_left A.natDegree B.natDegree).trans hcap
    rwa [←hA,natDegree_pow] at h
  have h₂ : p * W.natDegree ≤ p := by
    have h := (le_max_right A.natDegree B.natDegree).trans hcap
    rwa [←hB,natDegree_pow] at h
  have hU : U.natDegree ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by simpa only [mul_one] using h₁) hp
  have hW : W.natDegree ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by simpa only [mul_one] using h₂) hp
  have hNot : ¬(U.natDegree=0 ∧ W.natDegree=0) := by
    rintro ⟨hu,hw⟩
    have zA : A.natDegree = 0 := by rw [←hA,natDegree_pow,hu,mul_zero]
    have zB : B.natDegree = 0 := by rw [←hB,natDegree_pow,hw,mul_zero]
    rw [zA,zB,max_self] at hne
    exact (Nat.lt_irrefl 0) hne
  exact ⟨hU,hW,by omega⟩

end ActualGaussianWeberNormalizedAbscissaDegree318
