module

public import QuarticOptimization

/-! A typed sparse representation for a concrete integer-coefficient quartic.
The syntax itself restricts every residual term to coordinate degree at most
two. The parameter S is a coefficient, never an extra witness coordinate. -/

public section

namespace SparseQuartic

inductive Monomial (n : ℕ) where
  | one
  | linear (i : Fin n)
  | quadratic (i j : Fin n)
  deriving DecidableEq

structure Term (n : ℕ) where
  coefficient : ℤ
  parameterPower : ℕ
  monomial : Monomial n
  deriving DecidableEq

@[expose] noncomputable def monomialPolynomial {n : ℕ} : Monomial n → MvPolynomial (Fin n) ℤ
  | .one => 1
  | .linear i => MvPolynomial.X i
  | .quadratic i j => MvPolynomial.X i * MvPolynomial.X j

@[expose] noncomputable def termPolynomial {n : ℕ} (S : ℤ) (t : Term n) :
    MvPolynomial (Fin n) ℤ :=
  MvPolynomial.C (t.coefficient*S^t.parameterPower) * monomialPolynomial t.monomial

@[expose] noncomputable def residualPolynomial {n : ℕ} (S : ℤ) (ts : List (Term n)) :
    MvPolynomial (Fin n) ℤ := (ts.map (termPolynomial S)).sum

@[expose] noncomputable def polynomial {n : ℕ} (S : ℤ) (rows : List (List (Term n))) :
    MvPolynomial (Fin n) ℤ :=
  (rows.map (fun ts => (residualPolynomial S ts)^2)).sum

@[expose] def monomialValue {n : ℕ} (w : Fin n → ℚ) : Monomial n → ℚ
  | .one => 1
  | .linear i => w i
  | .quadratic i j => w i*w j

@[expose] def termValue {n : ℕ} (S : ℤ) (w : Fin n → ℚ) (t : Term n) : ℚ :=
  ((t.coefficient*S^t.parameterPower : ℤ) : ℚ) * monomialValue w t.monomial

@[expose] def residualValue {n : ℕ} (S : ℤ) (w : Fin n → ℚ) (ts : List (Term n)) : ℚ :=
  (ts.map (termValue S w)).sum

@[expose] def Constraints {n : ℕ} (S : ℤ) (rows : List (List (Term n)))
    (w : Fin n → ℚ) : Prop := ∀ ts ∈ rows, residualValue S w ts = 0

theorem monomial_degree {n : ℕ} (m : Monomial n) :
    (monomialPolynomial m).totalDegree ≤ 2 := by
  cases m with
  | one => simp [monomialPolynomial]
  | linear i => simp [monomialPolynomial]
  | quadratic i j =>
    simpa [monomialPolynomial] using
      MvPolynomial.totalDegree_mul (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)
        (MvPolynomial.X j)

theorem term_degree {n : ℕ} (S : ℤ) (t : Term n) :
    (termPolynomial S t).totalDegree ≤ 2 := by
  have h := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (t.coefficient*S^t.parameterPower) : MvPolynomial (Fin n) ℤ)
    (monomialPolynomial t.monomial)
  simp only [MvPolynomial.totalDegree_C, zero_add] at h
  exact h.trans (monomial_degree t.monomial)

theorem residual_degree {n : ℕ} (S : ℤ) (ts : List (Term n)) :
    (residualPolynomial S ts).totalDegree ≤ 2 := by
  induction ts with
  | nil => simp [residualPolynomial]
  | cons t ts ih =>
    simpa only [residualPolynomial, List.map_cons, List.sum_cons] using
      (MvPolynomial.totalDegree_add (termPolynomial S t)
        (residualPolynomial S ts)).trans (max_le (term_degree S t) ih)

theorem polynomial_degree {n : ℕ} (S : ℤ) (rows : List (List (Term n))) :
    (polynomial S rows).totalDegree ≤ 4 := by
  induction rows with
  | nil => simp [polynomial]
  | cons ts rows ih =>
    have hpow : ((residualPolynomial S ts)^2).totalDegree ≤ 4 :=
      (MvPolynomial.totalDegree_pow (residualPolynomial S ts) 2).trans
        (by have h := residual_degree S ts; omega)
    simpa only [polynomial, List.map_cons, List.sum_cons] using
      (MvPolynomial.totalDegree_add ((residualPolynomial S ts)^2)
        (polynomial S rows)).trans (max_le hpow ih)

theorem eval_monomial {n : ℕ} (w : Fin n → ℚ) (m : Monomial n) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w (monomialPolynomial m) =
      monomialValue w m := by
  cases m <;> simp [monomialPolynomial, monomialValue]

theorem eval_term {n : ℕ} (S : ℤ) (w : Fin n → ℚ) (t : Term n) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w (termPolynomial S t) =
      termValue S w t := by
  simp only [termPolynomial, termValue, map_mul, MvPolynomial.eval₂Hom_C,
    eval_monomial]
  simp

theorem eval_residual {n : ℕ} (S : ℤ) (w : Fin n → ℚ) (ts : List (Term n)) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w (residualPolynomial S ts) =
      residualValue S w ts := by
  simp only [residualPolynomial, residualValue, map_list_sum, List.map_map,
    Function.comp_def, eval_term]

theorem polynomial_zero_iff {n : ℕ} (S : ℤ) (rows : List (List (Term n)))
    (w : Fin n → ℚ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w (polynomial S rows) = 0 ↔
      Constraints S rows w := by
  have heval : MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w (polynomial S rows) =
      (rows.map (fun ts => (residualValue S w ts)^2)).sum := by
    simp only [polynomial, map_list_sum, List.map_map, Function.comp_def,
      map_pow, eval_residual]
  rw [heval]
  simpa [Constraints, List.map_map, Function.comp_def] using
    QuarticOptimization.rational_sum_squares_zero (rows.map (residualValue S w))

theorem polynomial_witnesses_iff {n : ℕ} (S : ℤ)
    (rows : List (List (Term (n+1)))) (q : ℚ) :
    (∃ w : Fin n → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) (polynomial S rows) = 0) ↔
    ∃ w : Fin n → ℚ, Constraints S rows (Fin.cons q w) := by
  simp only [polynomial_zero_iff]

end SparseQuartic
