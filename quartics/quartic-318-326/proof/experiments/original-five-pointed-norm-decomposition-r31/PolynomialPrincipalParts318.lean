module
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

public section
noncomputable section
namespace PolynomialPrincipalParts318
open Polynomial
set_option maxHeartbeats 500000
variable {K : Type*} [Field K]

/-- A denominator invertible at zero is coprime to the original coordinate. -/
theorem coprime_coordinate (D : K[X]) (hD : D.eval 0 ≠ 0) : IsCoprime (X : K[X]) D := by
  apply (EuclideanDomain.dvd_or_coprime X D Polynomial.irreducible_X).resolve_left
  rintro ⟨Q,hQ⟩
  apply hD
  rw [hQ,eval_mul,eval_X,zero_mul]

/-- Exact bounded principal-part numerator, before evaluating or dividing.
The second summand has no pole at the original coordinate zero. -/
theorem decomposition (D P : K[X]) (hD : D.eval 0 ≠ 0) (n m : ℕ) :
    ∃ R S : K[X], R.degree < (n : WithBot ℕ) ∧
      P = R * D^m + S * X^n := by
  have hcop : IsCoprime ((X : K[X])^n) (D^m) := (coprime_coordinate D hD).pow
  obtain ⟨a,b,hab⟩ := hcop
  let R := (P*b) %ₘ (X^n)
  let Q := (P*b) /ₘ (X^n)
  refine ⟨R,P*a+Q*D^m,?_,?_⟩
  · simpa only [degree_X_pow] using degree_modByMonic_lt (P*b) (monic_X_pow n)
  · have hrem : R + X^n*Q = P*b := modByMonic_add_div (P*b) (X^n)
    linear_combination -P * hab - D^m * hrem

end PolynomialPrincipalParts318
