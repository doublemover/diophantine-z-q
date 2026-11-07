module
public import QuarticOptimization
public section
namespace ConcreteQuadraticDomains
open QuarticOptimization

theorem seven_times_square_ne_one (q : ℚ) : 7*q^2 ≠ 1 := by
  intro h
  have hsf : Squarefree (7 : ℕ) := by
    intro d hd
    have hle : d*d ≤ 7 := Nat.le_of_dvd (by decide) hd
    have hdle : d ≤ 2 := by nlinarith
    interval_cases d <;> norm_num at *
  obtain ⟨z, hz⟩ := squarefree_multiple_square_integral q 7
    hsf 1 (by simpa using h)
  rw [← hz] at h
  have hi : 7*z^2 = (1 : ℤ) := by exact_mod_cast h
  omega

@[expose] def quarticReal (a b : ℚ) : ℚ :=
  11*(a^2+2*b^2)^2+22*(2*a*b)^2-24*(a^2+2*b^2)*(2*a*b)

@[expose] def quarticImag (a b : ℚ) : ℚ :=
  22*(a^2+2*b^2)*(2*a*b)-6*(a^2+2*b^2)^2-12*(2*a*b)^2

theorem norm_quartic_identity (a b : ℚ) :
    quarticReal a b ^2 - 2*quarticImag a b ^2 =
      (7*(a^2-2*b^2)^2)^2 := by
  unfold quarticReal quarticImag
  ring

theorem reciprocal_ordinate_nonzero (a b v0 v1 : ℚ)
    (h0 : v0^2+2*v1^2+quarticReal a b = 1)
    (h1 : 2*v0*v1+quarticImag a b = 0) : v0 ≠ 0 ∨ v1 ≠ 0 := by
  by_contra hz
  push_neg at hz
  obtain ⟨hv0,hv1⟩ := hz
  simp only [hv0,hv1,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add] at h0 h1
  have hn := norm_quartic_identity a b
  rw [h0,h1] at hn
  have heq : 7*(a^2-2*b^2)^2 = 1 := by
    have hnonneg : 0 ≤ 7*(a^2-2*b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
    nlinarith
  exact seven_times_square_ne_one (a^2-2*b^2) heq


theorem two_times_square_ne_one (q : ℚ) : 2*q^2 ≠ 1 := by
  intro h
  obtain ⟨z,hz⟩ := twice_square_integral q 1 (by simpa using h)
  rw [← hz] at h
  have hi : 2*z^2=(1 : ℤ) := by exact_mod_cast h
  omega

theorem norm_nonzero_of_real_nonzero (a b : ℚ) (ha : a ≠ 0) :
    a^2-2*b^2 ≠ 0 := by
  intro hn
  have hq : 2*(b/a)^2 = 1 := by
    field_simp [ha]
    nlinarith
  exact two_times_square_ne_one (b/a) hq

end ConcreteQuadraticDomains
