module
public import OriginalSexticIntegralTower318

/-! Polynomial coefficient reflection in the exact integer tower; no native
decide shortcut. This module never assumes field relations beyond the named
three from the lifted arithmetic coordinates. -/
public section
noncomputable section

namespace OriginalSexticCoefficientAudit318

open Polynomial OriginalSexticIntegralTower318
open scoped BigOperators

abbrev Table (n : ℕ) := Fin (n + 1) → V8

@[expose] def coeff {n : ℕ} (xs : Table n) (i : ℕ) : V8 :=
  if h : i < n+1 then xs ⟨i,h⟩ else 0

@[expose] def convolve (A B : ℤ) (R : V4) (xs ys : ℕ → V8) (i : ℕ) : V8 :=
  ∑ j ∈ Finset.range (i+1), m8 A B R (xs j) (ys (i-j))

@[expose] def cdiff (xs : ℕ → V8) (i : ℕ) : V8 := ((i+1 : ℕ) : ℤ) • xs (i+1)

@[expose] def shift (xs : ℕ → V8) (k i : ℕ) : V8 :=
  if k ≤ i then xs (i-k) else 0

@[expose] def constantCoeff (v : V8) (i : ℕ) : V8 := if i=0 then v else 0

variable {E : Type*} [Field E]

@[expose] def readPoly (r : V8 →+ E) {n : ℕ} (xs : Table n) : E[X] :=
  ∑ i ∈ Finset.range (n+1), monomial i (r (coeff xs i))

@[simp] theorem readPoly_coeff (r : V8 →+ E) {n : ℕ} (xs : Table n) (i : ℕ) :
    (readPoly r xs).coeff i = r (coeff xs i) := by
  rw [readPoly, finsetSum_coeff]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split
  · rfl
  · simp [coeff, *]

theorem readPoly_degree (r : V8 →+ E) {n : ℕ} (xs : Table n) :
    (readPoly r xs).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [readPoly_coeff, coeff, dite_eq_right (by omega), map_zero]

theorem read_zsmul (r : V8 →+ E) (c : ℤ) (x : V8) : r (c • x) = (c:E)*r x := by
  rw [map_zsmul, zsmul_eq_mul]

@[simp] theorem readPoly_diff (r : V8 →+ E) {n : ℕ} (xs : Table n) (i : ℕ) :
    (readPoly r xs).derivative.coeff i = r (cdiff (coeff xs) i) := by
  rw [coeff_derivative, readPoly_coeff, cdiff, read_zsmul]
  push_cast
  ring

theorem read_convolve (r : V8 →+ E) (A B : ℤ) (R : V4)
    (hm : ∀ u v, r (m8 A B R u v) = r u * r v)
    (xs ys : ℕ → V8) (p q : E[X]) (hp : ∀ i, p.coeff i = r (xs i))
    (hq : ∀ i, q.coeff i = r (ys i)) (i : ℕ) :
    (p*q).coeff i = r (convolve A B R xs ys i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j k => p.coeff j * q.coeff k)]
  simp only [convolve, map_sum, hm, hp, hq]

theorem read_shift (r : V8 →+ E) (xs : ℕ → V8) (p : E[X])
    (hp : ∀ i, p.coeff i = r (xs i)) (k i : ℕ) :
    (X ^ k * p).coeff i = r (shift xs k i) := by
  by_cases h : k ≤ i
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k j, coeff_X_pow_mul, shift, ite_eq_left (by omega), Nat.add_sub_cancel, hp]
  · rw [shift, ite_eq_right h, map_zero]
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have he := (Finset.mem_antidiagonal.mp hx)
    rw [coeff_X_pow, ite_eq_right (by omega), zero_mul]

theorem read_constant (r : V8 →+ E) (v : V8) (i : ℕ) :
    (C (r v)).coeff i = r (constantCoeff v i) := by
  by_cases h : i = 0
  · simp [h, constantCoeff]
  · simp [h, constantCoeff, coeff_C]

theorem eq_of_upto (p q : E[X]) (n : ℕ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ i : Fin (n+1), p.coeff i = q.coeff i) : p=q := by
  ext i
  by_cases hi : i < n+1
  · exact h ⟨i,hi⟩
  · rw [natDegree_le_iff_coeff_eq_zero.mp hp _ (by omega),
      natDegree_le_iff_coeff_eq_zero.mp hq _ (by omega)]

end OriginalSexticCoefficientAudit318

#print axioms OriginalSexticCoefficientAudit318.read_convolve
#print axioms OriginalSexticCoefficientAudit318.eq_of_upto
