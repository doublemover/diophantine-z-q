module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Exact scalar reads in the original polarized quotient chart. The chart's
identification, its two actual Hodge coframes and raw Kodaira–Spencer map are
geometric producers, not supplied by these polynomial identities. -/

public section
namespace OriginalPolarizedContactGauge318

section Polynomials
variable {R : Type*} [CommRing R]

@[expose] def f (z : R) : R :=
  43*z^4 + 600*z^3 + 986*z^2 - 600*z + 43

@[expose] def n (z : R) : R :=
  10976*(1 + z^2)^2

@[expose] def g (z : R) : R :=
  z^4 + 14*z^3 + 23*z^2 - 14*z + 1

@[expose] def h (z : R) : R :=
  43904*z*(1+z^2)*f z - n z*(172*z^3 + 1800*z^2 + 1972*z - 600)

@[expose] def p (T : R) : R :=
  T * (T-32) * (T-76832) * (T+343)

@[expose] def pnum (z : R) : R :=
  n z * (n z - 32*f z) * (n z - 76832*f z) * (n z + 343*f z)

theorem contact_32 (z : R) : n z - 32*f z = 9600*(z^2-z-1)^2 := by
  unfold n f
  ring

theorem contact_76832 (z : R) : n z - 76832*f z = -3292800*g z := by
  unfold n f g
  ring

theorem contact_neg343 (z : R) : n z + 343*f z = 25725*(z^2+4*z-1)^2 := by
  unfold n f
  ring

theorem tangent (z : R) : h z = 6585600*(1+z^2)*(z^2-z-1)*(z^2+4*z-1) := by
  unfold h n f
  ring

theorem theta_cross (z : R) : (-12600)*pnum z = 2593080000*g z*h z^2 := by
  unfold pnum
  rw [contact_32, contact_76832, contact_neg343, tangent]
  unfold n
  ring

theorem algebraic_cross (z : R) : (-10080)*pnum z = 2074464000*g z*h z^2 := by
  unfold pnum
  rw [contact_32, contact_76832, contact_neg343, tangent]
  unfold n
  ring
end Polynomials

section Field
variable {K : Type*} [Field K]

theorem p_read (z : K) (hf : f z ≠ 0) :
    p (n z / f z) = pnum z / f z^4 := by
  unfold p pnum
  field_simp

private theorem of_cross (z k d : K)
    (hf : f z ≠ 0) (hg : g z ≠ 0) (hh : h z ≠ 0)
    (cross : k * pnum z = d * g z * h z^2) :
    (p (n z / f z) * (k * f z^3 / (g z * h z^2)))⁻¹ = f z / d := by
  have hh2 := pow_ne_zero 2 hh
  have hx : p (n z / f z) * (k * f z^3 / (g z * h z^2)) = d / f z := by
    rw [p_read z hf]
    calc
      _ = (k * pnum z)/(f z * g z * h z^2) := by
        field_simp
      _ = d / f z := by
        rw [cross]
        field_simp
  rw [hx, inv_div]

/-- In the calibrated Nagano theta coframe, the raw coefficient is the
second factor shown; the resulting actual scalar has no derivative left. -/
theorem theta_read (z : K) (hf : f z ≠ 0) (hg : g z ≠ 0) (hh : h z ≠ 0) :
    (p (n z / f z) * ((-12600) * f z^3 / (g z * h z^2)))⁻¹ =
      f z / 2593080000 :=
  of_cross z _ _ hf hg hh (theta_cross z)

/-- Same raw map in the algebraic Igusa-Clebsch coframe. -/
theorem algebraic_read (z : K) (hf : f z ≠ 0) (hg : g z ≠ 0) (hh : h z ≠ 0) :
    (p (n z / f z) * ((-10080) * f z^3 / (g z * h z^2)))⁻¹ =
      f z / 2074464000 :=
  of_cross z _ _ hf hg hh (algebraic_cross z)
variable [CharZero K]

theorem other_denominators (z : K) (hf : f z ≠ 0)
    (hp : p (n z / f z) ≠ 0) : g z ≠ 0 ∧ h z ≠ 0 := by
  have hpnum : pnum z ≠ 0 := by
    intro hz
    exact hp (by rw [p_read z hf, hz, zero_div])
  constructor
  · intro hz
    apply hpnum
    unfold pnum
    rw [contact_76832, hz, mul_zero, mul_zero, zero_mul]
  · intro hz
    have hc := theta_cross z
    rw [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] at hc
    exact hpnum ((mul_eq_zero.mp hc).resolve_left (by norm_num))

/-- Finite-chart specialization of the globally usable rescaled theta
coframe. The scalar denominator only uses the same literal T. -/
theorem theta_scaled_read (z : K) (hf : f z ≠ 0)
    (hp : p (n z / f z) ≠ 0) :
    (p (n z / f z) *
      ((1+z^2)^2 * ((-12600) * f z^3 / (g z * h z^2))))⁻¹ =
        1 / (236250 * (n z / f z)) := by
  obtain ⟨hg,hh⟩ := other_denominators z hf hp
  have hq : 1+(z:K)^2 ≠ 0 := by
    intro hz
    have : n z = 0 := by unfold n; rw [hz]; ring
    apply hp
    rw [this, zero_div]
    unfold p
    ring
  have hq2 := pow_ne_zero 2 hq
  rw [show p (n z / f z) * ((1+z^2)^2 * ((-12600) *
      f z^3 / (g z * h z^2))) = (p (n z / f z) * ((-12600) *
      f z^3 / (g z * h z^2))) * (1+z^2)^2 by ring,
    mul_inv_rev, theta_read z hf hg hh]
  unfold n
  field_simp
  ring
end Field

end OriginalPolarizedContactGauge318

#print axioms OriginalPolarizedContactGauge318.theta_read
#print axioms OriginalPolarizedContactGauge318.algebraic_read
#print axioms OriginalPolarizedContactGauge318.theta_scaled_read
