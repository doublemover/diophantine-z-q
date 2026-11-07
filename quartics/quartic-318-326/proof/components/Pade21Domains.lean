module
public import PadeDenominatorNonvanishing
public section
namespace Pade21Domains
open ConcreteG8Domain PadeDenominatorNonvanishing

/-- Rational square-gap tests for n and 2n exclude n as a square in Q(√2). -/
theorem K_square_gap (n k l : ℤ) (hk : 0≤k) (hl : 0≤l)
    (hk0 : k^2<n) (hk1 : n<(k+1)^2)
    (hl0 : l^2<2*n) (hl1 : 2*n<(l+1)^2) (x : K) : x^2 ≠ (n : K) := by
  have hq (q : ℚ) : q^2 ≠ (n : ℚ) := rational_square_gap q n k hk hk0 hk1
  have hh (q : ℚ) : 2*q^2 ≠ (n : ℚ) := by
    intro h
    apply rational_square_gap (2*q) (2*n) l hl hl0 hl1
    push_cast
    nlinarith
  simpa using quadratic_field_nonsquare (n : ℚ) hq hh x

theorem no_square_21009 (x : K) : x^2 ≠ 21009 :=
  K_square_gap 21009 144 204 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
theorem no_square_2856 (x : K) : x^2 ≠ 2856 :=
  K_square_gap 2856 53 75 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
theorem no_square_91 (x : K) : x^2 ≠ 91 :=
  K_square_gap 91 9 13 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x

theorem square_not_negative (n : ℚ) (hn : n<0) (x : K) :
    x^2 ≠ algebraMap ℚ K n := by
  rcases x with ⟨a,b⟩
  intro hx
  have hr : a^2+2*b^2=n := by
    simpa [pow_two,mul_assoc] using congrArg QuadraticAlgebra.re hx
  nlinarith [sq_nonneg a,sq_nonneg b]

@[expose] def PG {F : Type*} [Field F] (x : F) : F :=
  1-(61/65)*x+(16/195)*x^2
@[expose] def QG {F : Type*} [Field F] (x : F) : F := 1-(7/13)*x
@[expose] def PJ {F : Type*} [Field F] (x : F) : F :=
  1+(12/65)*x-(2/195)*x^2
@[expose] def QJ {F : Type*} [Field F] (x : F) : F := 1+(5/13)*x

theorem PG_nonzero (x : K) : PG x ≠ 0 := by
  intro hx
  apply no_square_21009 (32*x-183)
  unfold PG at hx
  linear_combination (64*195)*hx

theorem PJ_nonzero (x : K) : PJ x ≠ 0 := by
  intro hx
  apply no_square_2856 (-4*x+36)
  unfold PJ at hx
  linear_combination (-8*195)*hx

/-- The G denominator is not globally nonzero: the square-argument hypothesis
is essential and is satisfied by D*f²=(d*f)² in the actual source. -/
theorem QG_nonzero_on_square (y : K) : QG (y^2) ≠ 0 := by
  intro hx
  apply no_square_91 (7*y)
  unfold QG at hx
  linear_combination (-91)*hx

/-- The J denominator is nonzero on the actual reciprocal curve domain. -/
theorem QJ_nonzero_on_circle (v y : K) (hc : v^2+y^2=1) :
    QJ (v-1) ≠ 0 := by
  intro hx
  have hv : v=(-8/5 : K) := by
    unfold QJ at hx
    linear_combination (13/5 : K)*hx
  rw [hv] at hc
  apply square_not_negative (-39/25) (by norm_num) y
  norm_num at hc ⊢
  linear_combination hc

end Pade21Domains
