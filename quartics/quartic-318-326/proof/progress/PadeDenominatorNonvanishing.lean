module
public import ConcreteG8Domain
public section
namespace PadeDenominatorNonvanishing
open ConcreteG8Domain

/-- A rational square lying strictly between consecutive integer squares is impossible. -/
theorem rational_square_gap (q : ℚ) (n k : ℤ) (hk : 0 ≤ k)
    (hlo : k^2<n) (hhi : n<(k+1)^2) : q^2 ≠ (n : ℚ) := by
  intro hq
  obtain ⟨z,hz⟩ := QuarticOptimization.squarefree_multiple_square_integral q 1
    (by norm_num) n (by simpa using hq)
  rw [←hz] at hq
  have hn : z^2=n := by exact_mod_cast hq
  have ha : |z|^2=n := by simpa using hn
  by_cases hs : |z| ≤ k
  · have hp : 0 ≤ (k-|z|)*(k+|z|) := mul_nonneg (by omega) (by positivity)
    nlinarith
  · have hs : k+1 ≤ |z| := by omega
    have hp : 0 ≤ (|z|-(k+1))*(|z|+(k+1)) := mul_nonneg (by omega) (by positivity)
    nlinarith

theorem no_square_29920 (q : ℚ) : q^2 ≠ 29920 :=
  rational_square_gap q 29920 172 (by norm_num) (by norm_num) (by norm_num)
theorem no_square_14960 (q : ℚ) : q^2 ≠ 14960 :=
  rational_square_gap q 14960 122 (by norm_num) (by norm_num) (by norm_num)
theorem no_square_136 (q : ℚ) : q^2 ≠ 136 :=
  rational_square_gap q 136 11 (by norm_num) (by norm_num) (by norm_num)
theorem no_square_68 (q : ℚ) : q^2 ≠ 68 :=
  rational_square_gap q 68 8 (by norm_num) (by norm_num) (by norm_num)

theorem quadratic_field_nonsquare (n : ℚ)
    (hq : ∀ q : ℚ, q^2 ≠ n) (hh : ∀ q : ℚ, 2*q^2 ≠ n) (x : K) :
    x^2 ≠ algebraMap ℚ K n := by
  rcases x with ⟨a,b⟩
  intro hx
  have hr : a^2+2*b^2=n := by
    simpa [pow_two,mul_assoc] using congrArg QuadraticAlgebra.re hx
  have hi : 2*a*b=0 := by
    have hi' := congrArg QuadraticAlgebra.im hx
    simp [pow_two] at hi'
    nlinarith
  rcases mul_eq_zero.mp hi with ha | hb
  · have ha : a=0 := by exact (mul_eq_zero.mp ha).resolve_left (by norm_num)
    apply hh b
    simpa [ha] using hr
  · apply hq a
    simpa [hb] using hr

theorem K_no_square_29920 (x : K) : x^2 ≠ 29920 := by
  apply quadratic_field_nonsquare 29920 no_square_29920
  intro q h
  apply no_square_14960 q
  linarith

theorem K_no_square_136 (x : K) : x^2 ≠ 136 := by
  apply quadratic_field_nonsquare 136 no_square_136
  intro q h
  apply no_square_68 q
  linarith

@[expose] def QG {F : Type*} [Field F] (x : F) : F := 1-(22/21)*x+(11/51)*x^2
@[expose] def QJ {F : Type*} [Field F] (x : F) : F := 1+(2/3)*x+(5/51)*x^2

theorem QG_nonzero (x : K) : QG x ≠ 0 := by
  intro hx
  apply K_no_square_29920 (154*x-374)
  unfold QG at hx
  linear_combination (4*77*357)*hx

theorem QJ_nonzero (x : K) : QJ x ≠ 0 := by
  intro hx
  apply K_no_square_136 (10*x+34)
  unfold QJ at hx
  linear_combination (4*5*51)*hx
end PadeDenominatorNonvanishing
