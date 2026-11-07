module
public import SparseQuartic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public section
namespace ExactDegree
open SparseQuartic

@[expose] def avoids {n : ℕ} (i : Fin n) : Monomial n → Bool
  | .one => true
  | .linear j => decide (i ≠ j)
  | .quadratic j k => decide (i ≠ j ∧ i ≠ k)

@[expose] def rowAvoids {n : ℕ} (i : Fin n) (row : List (Term n)) : Bool :=
  row.all (fun t => avoids i t.monomial)

@[expose] def rowsAvoid {n : ℕ} (i : Fin n) (rows : List (List (Term n))) : Bool :=
  rows.all (rowAvoids i)

theorem monomial_degree_zero {n : ℕ} (i : Fin n) (m : Monomial n)
    (h : avoids i m = true) : (monomialPolynomial m).degreeOf i = 0 := by
  cases m with
  | one => simp [monomialPolynomial]
  | linear j =>
    have hij : i ≠ j := by simpa [avoids] using h
    simp [monomialPolynomial, MvPolynomial.degreeOf_X, hij]
  | quadratic j k =>
    have hij : i ≠ j ∧ i ≠ k := by simpa [avoids] using h
    apply Nat.eq_zero_of_le_zero
    simpa [monomialPolynomial, MvPolynomial.degreeOf_X, hij.1, hij.2] using
      MvPolynomial.degreeOf_mul_le i (MvPolynomial.X j : MvPolynomial (Fin n) ℤ) (MvPolynomial.X k)

theorem term_degree_zero {n : ℕ} (S : ℤ) (i : Fin n) (t : Term n)
    (h : avoids i t.monomial = true) : (termPolynomial S t).degreeOf i = 0 := by
  have hb := MvPolynomial.degreeOf_mul_le i
    (MvPolynomial.C (t.coefficient*S^t.parameterPower) : MvPolynomial (Fin n) ℤ)
    (monomialPolynomial t.monomial)
  rw [MvPolynomial.degreeOf_C, monomial_degree_zero i t.monomial h] at hb
  exact Nat.eq_zero_of_le_zero hb

theorem residual_degree_zero {n : ℕ} (S : ℤ) (i : Fin n) (row : List (Term n))
    (h : rowAvoids i row = true) : (residualPolynomial S row).degreeOf i = 0 := by
  induction row with
  | nil => simp [residualPolynomial]
  | cons t ts ih =>
    have ht : avoids i t.monomial = true ∧ rowAvoids i ts = true := by
      simpa [rowAvoids] using h
    have hb := MvPolynomial.degreeOf_add_le i (termPolynomial S t) (residualPolynomial S ts)
    rw [term_degree_zero S i t ht.1, ih ht.2] at hb
    change (termPolynomial S t + residualPolynomial S ts).degreeOf i = 0
    exact Nat.eq_zero_of_le_zero hb

theorem polynomial_degree_zero {n : ℕ} (S : ℤ) (i : Fin n)
    (rows : List (List (Term n))) (h : rowsAvoid i rows = true) :
    (polynomial S rows).degreeOf i = 0 := by
  induction rows with
  | nil => simp [polynomial]
  | cons r rs ih =>
    have hr : rowAvoids i r = true ∧ rowsAvoid i rs = true := by
      simpa [rowsAvoid] using h
    have hp : ((residualPolynomial S r)^2).degreeOf i = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [residual_degree_zero S i r hr.1] using
        MvPolynomial.degreeOf_pow_le i (residualPolynomial S r) 2
    have hb := MvPolynomial.degreeOf_add_le i ((residualPolynomial S r)^2) (polynomial S rs)
    rw [hp, ih hr.2] at hb
    change ((residualPolynomial S r)^2 + polynomial S rs).degreeOf i = 0
    exact Nat.eq_zero_of_le_zero hb

theorem polynomial_move_pivot {n : ℕ} (S : ℤ) (a b : List (List (Term n)))
    (p : List (Term n)) :
    polynomial S (a ++ p :: b) = (residualPolynomial S p)^2 + polynomial S (a++b) := by
  simp only [polynomial, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

theorem degree_exactly_four {n : ℕ} (S : ℤ) (i j : Fin n) (hij : i ≠ j)
    (a b : List (List (Term n))) (p : List (Term n))
    (hp : residualPolynomial S p = (MvPolynomial.X i)^2-MvPolynomial.X j)
    (hrest : rowsAvoid i (a++b) = true) :
    (polynomial S (a++p::b)).totalDegree = 4 := by
  have hrestdeg := polynomial_degree_zero S i (a++b) hrest
  have hneg : (-(MvPolynomial.X j : MvPolynomial (Fin n) ℤ)).degreeOf i = 0 := by
    simp [MvPolynomial.degreeOf_X, hij]
  have hpdeg : (residualPolynomial S p).degreeOf i = 2 := by
    rw [hp, sub_eq_add_neg]
    have hlt : (-(MvPolynomial.X j : MvPolynomial (Fin n) ℤ)).degreeOf i <
        ((MvPolynomial.X i : MvPolynomial (Fin n) ℤ)^2).degreeOf i := by simp [hneg]
    simpa using MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hlt
  have hpne : residualPolynomial S p ≠ 0 := by
    intro hz
    simp [hz] at hpdeg
  have hs : ((residualPolynomial S p)^2).degreeOf i = 4 := by
    rw [MvPolynomial.degreeOf_pow_eq i _ 2 hpne, hpdeg]
  have hdeg : (polynomial S (a++p::b)).degreeOf i = 4 := by
    rw [polynomial_move_pivot]
    have hlt : (polynomial S (a++b)).degreeOf i < ((residualPolynomial S p)^2).degreeOf i := by
      rw [hrestdeg, hs]; decide
    rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hlt, hs]
  have hlo := MvPolynomial.degreeOf_le_totalDegree (polynomial S (a++p::b)) i
  have hhi := SparseQuartic.polynomial_degree S (a++p::b)
  omega

end ExactDegree
