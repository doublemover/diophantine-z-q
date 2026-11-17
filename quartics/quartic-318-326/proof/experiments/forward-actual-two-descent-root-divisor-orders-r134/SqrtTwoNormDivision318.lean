module
public import Mathlib.Algebra.Order.Round
public import Mathlib.Tactic
public section
namespace SqrtTwoNormDivision318

private theorem square_le_quarter (x : ℚ) (h : |x| ≤ 1/2) : x^2 ≤ 1/4 := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hm := mul_nonneg (show (0:ℚ) ≤ 1/2-x by linarith)
    (show (0:ℚ) ≤ 1/2+x by linarith)
  nlinarith

/-- Rounding both rational coefficients gives a strict approximation for
the absolute norm of Q(sqrt2), despite the norm being indefinite. -/
theorem norm_approximation (a b : ℚ) :
    ∃ m n : ℤ, |(a-m)^2-2*(b-n)^2| < 1 := by
  refine ⟨round a, round b, ?_⟩
  have ha := square_le_quarter (a-round a) (abs_sub_round a)
  have hb := square_le_quarter (b-round b) (abs_sub_round b)
  apply abs_lt.mpr
  constructor <;> nlinarith [sq_nonneg (a-round a), sq_nonneg (b-round b)]

/-- Concrete norm-Euclidean division in Z[sqrt2]. The quotient is an actual
integer pair obtained by rounding the coefficients of the rational quotient.
This is descent machinery, not a rational local-global theorem. -/
theorem norm_division (a b c d : ℤ) (hN : c^2-2*d^2 ≠ 0) :
    ∃ m n : ℤ,
      |(a-(m*c+2*n*d))^2-2*(b-(m*d+n*c))^2| < |c^2-2*d^2| := by
  have hNq : (c:ℚ)^2-2*(d:ℚ)^2 ≠ 0 := by exact_mod_cast hN
  let A : ℚ := ((a:ℚ)*c-2*b*d)/((c:ℚ)^2-2*d^2)
  let B : ℚ := ((b:ℚ)*c-a*d)/((c:ℚ)^2-2*d^2)
  obtain ⟨m,n,hmn⟩ := norm_approximation A B
  refine ⟨m,n,?_⟩
  have he : ((a:ℚ)-((m:ℚ)*c+2*(n:ℚ)*d))^2-2*((b:ℚ)-((m:ℚ)*d+(n:ℚ)*c))^2 =
      ((c:ℚ)^2-2*d^2)*((A-m)^2-2*(B-n)^2) := by
    dsimp only [A,B]
    field_simp [hNq] <;> ring
  have hrem : |((a:ℚ)-((m:ℚ)*c+2*(n:ℚ)*d))^2-2*((b:ℚ)-((m:ℚ)*d+(n:ℚ)*c))^2| <
      |(c:ℚ)^2-2*d^2| := by
    rw [he, abs_mul]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hmn (abs_pos.mpr hNq)
  exact_mod_cast hrem

end SqrtTwoNormDivision318
