module
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualLinearQArithmeticCalibration318

/-- Original rational five-root contact polynomial, not an arbitrary
polynomial considered modulo the new prime. -/
@[expose] def contact (T : ℚ) : ℚ := T*(T+1/2)*(T+1)*(T-1/2399)*(T+32/407)
@[expose] def time (u A q : ℚ) : ℚ := u/(A^2*q)
@[expose] def parameter (c u A q : ℚ) : ℚ := c^2*time u A q
@[expose] def delta (c u A q : ℚ) : ℚ := parameter c u A q-1

@[expose] def factorProduct (c u A q : ℚ) : ℚ :=
  u*(u+(1/2)*(A^2*q)/c^2)*(u+(A^2*q)/c^2)*
    (u-(1/2399)*(A^2*q)/c^2)*(u+(32/407)*(A^2*q)/c^2)

@[expose] def weight (c u A q : ℚ) : ℚ :=
  c^10*((delta c u A q)^2/contact (parameter c u A q))

@[expose] def pole (τ c u A q : ℚ) : ℚ :=
  τ^2*contact (parameter c u A q)/(c^10*(delta c u A q)^6)

theorem contact_product (c u A q : ℚ) (hc : c ≠ 0) (hA : A ≠ 0) (hq : q ≠ 0) :
    contact (parameter c u A q) = c^10/(A^2*q)^5*factorProduct c u A q := by
  unfold contact parameter time factorProduct
  field_simp [hc,hA,hq] <;> ring

/-- The actual additional prime occurs with odd POSITIVE exponent in
the square class, independently of the trace quotient's value. -/
theorem pole_squareclass (τ c u A q : ℚ) (hc : c ≠ 0) (hA : A ≠ 0)
    (hq : q ≠ 0) (hΔ : delta c u A q ≠ 0) :
    pole τ c u A q = q*factorProduct c u A q*(τ/(A^5*q^3*(delta c u A q)^3))^2 := by
  rw [pole,contact_product c u A q hc hA hq]
  field_simp [hc,hA,hq,hΔ] <;> ring

end ActualLinearQArithmeticCalibration318
