module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Division-free two-place weight for the original (4.7)

The denominator in this file is a token, not an assertion that it is
invertible in the coefficient ring.  Only the odd prime is inverted.
-/

public section

namespace OriginalRCSupportWeightIdentity318

variable {R : Type*} [CommRing R]

/-- This half is computed over the integers, not in a finite stage. -/
@[expose] def integerHalf (q : ℕ) : ℤ := ((q:ℤ)-1)/2

theorem two_mul_integerHalf (q : ℕ) (hq : q % 2 = 1) :
    2 * integerHalf q = (q:ℤ)-1 := by
  have h : q = 2*(q/2)+1 := by
    have hn := Nat.mod_add_div q 2
    omega
  have hz := congrArg (fun n : ℕ => (n : ℤ)) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one] at hz
  unfold integerHalf
  omega

/-- The canonical odd-prime unit at a finite dyadic coefficient stage,
including further coefficient algebras via their scalar ring homomorphism. -/
def finiteOddUnit (M q : ℕ) (hq : q % 2 = 1)
    (f : ZMod (2^M) →+* R) : Rˣ := by
  have hnd : ¬ (2:ℕ) ∣ q := by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  have hc : Nat.Coprime q 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd).symm
  exact Units.map f.toMonoidHom (ZMod.unitOfCoprime q (hc.pow_right M))

@[simp]
theorem finiteOddUnit_coe (M q : ℕ) (hq : q % 2 = 1)
    (f : ZMod (2^M) →+* R) : (finiteOddUnit M q hq f : R) = q := by
  simp [finiteOddUnit, ZMod.coe_unitOfCoprime]

/-- The two inverse Floquet/Frobenius orientations occur exactly once. -/
@[expose] def signedSum (z : Rˣ) : R := (z:R) + (↑z⁻¹:R)

@[expose] def normToken (a : R) (z : Rˣ) : R := a - signedSum z

@[expose] def denominator (a : R) (z : Rˣ) : R := (normToken a z)^2

/-- The product of the two rank-two local determinant polynomials. -/
@[expose] def euler (a : R) (Q z : Rˣ) : R :=
  (↑Q⁻¹:R)^2 * (((z:R)^2 - a*(z:R) + (Q:R)) *
    ((↑z⁻¹:R)^2 - a*(↑z⁻¹:R) + (Q:R)))

@[expose] def correction (q : ℕ) (a : R) (Q z : Rˣ) : R :=
  (integerHalf q : R) * (↑Q⁻¹:R)^2 *
    (-((Q:R)+1)*denominator a z + ((Q:R)-1) - signedSum z * normToken a z)

/-- A_q = e_q² + (1+g_q)w_q, still before every localization. -/
@[expose] def numerator (q : ℕ) (a : R) (Q g z : Rˣ) : R :=
  denominator a z + (1+(g:R))*correction q a Q z

private theorem unit_pow_two (Q : Rˣ) : (Q:R)^2 * (↑Q⁻¹:R)^2 = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

theorem euler_cleared (a : R) (Q z : Rˣ) :
    (Q:R)^2 * euler a Q z = denominator a z +
      ((Q:R)-1)*(((Q:R)-1)-signedSum z*normToken a z) := by
  let x : R := z
  let y : R := ↑z⁻¹
  let q : R := Q
  have hxy : x*y=1 := Units.mul_inv z
  have hpoly :
      (x^2-a*x+q)*(y^2-a*y+q) =
        (a-(x+y))^2 + (q-1)*((q-1)-(x+y)*(a-(x+y))) := by
    calc
      _ = (a-(x+y))^2 + (q-1)*((q-1)-(x+y)*(a-(x+y))) +
            (x*y-1)*(x*y+1-a*(x+y)-2*q+a^2) := by ring
      _ = _ := by rw [hxy, sub_self, zero_mul, add_zero]
  rw [euler, ← mul_assoc, unit_pow_two, one_mul]
  exact hpoly

/-- The doubled token is l_q - e_q², proved without canceling two. -/
theorem twice_correction (q : ℕ) (hq : q % 2 = 1) (a : R) (Q z : Rˣ)
    (hQ : (Q:R) = q) :
    2 * correction q a Q z = euler a Q z - denominator a z := by
  have hh := congrArg (fun m : ℤ => (m:R)) (two_mul_integerHalf q hq)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_one,
    Int.cast_natCast] at hh
  have hhalf : (2:R)*(integerHalf q:R)=(Q:R)-1 := hh.trans (by rw [hQ])
  have hQ' : (↑Q⁻¹:R)^2 * (Q:R)^2 = 1 := by
    rw [mul_comm, unit_pow_two]
  calc
    2 * correction q a Q z = ((2:R)*(integerHalf q:R))*(↑Q⁻¹:R)^2 *
        (-((Q:R)+1)*denominator a z + ((Q:R)-1) - signedSum z * normToken a z) := by
          unfold correction
          ring
    _ = (↑Q⁻¹:R)^2 * ((Q:R)^2 * (euler a Q z - denominator a z)) := by
      rw [hhalf, mul_sub ((Q:R)^2) (euler a Q z) (denominator a z), euler_cleared]
      ring
    _ = _ := by rw [← mul_assoc, hQ', one_mul]

private theorem signedSum_shift (g z : Rˣ) (hg : (g:R)^2=1) :
    signedSum (g*z) = (g:R)*signedSum z := by
  have hginv : (↑g⁻¹:R) = (g:R) := by
    calc
      (↑g⁻¹:R) = (↑g⁻¹:R)*(g:R)^2 := by rw [hg, mul_one]
      _ = (g:R) := by rw [pow_two, ← mul_assoc, Units.inv_mul, one_mul]
  simp only [signedSum, Units.val_mul, mul_inv_rev, hginv]
  ring

/-- Changing the Frobenius lift by the original involution preserves
the ratio as a cross-product, even at a finite dyadic quotient. -/
theorem lift_cross_mul (q : ℕ) (a : R) (Q g z : Rˣ) (hg : (g:R)^2=1) :
    numerator q a Q g (g*z) * denominator a z =
      numerator q a Q g z * denominator a (g*z) := by
  let s := signedSum z
  let dB := -2*a*s + ((g:R)+1)*s^2
  let dW := (integerHalf q : R)*(↑Q⁻¹:R)^2 *
    (-((Q:R)+1)*dB - (a*s-((g:R)+1)*s^2))
  have hB : denominator a (g*z) - denominator a z = ((g:R)-1)*dB := by
    simp only [denominator, normToken, signedSum_shift g z hg, dB, s]
    ring
  have hW : correction q a Q (g*z) - correction q a Q z = ((g:R)-1)*dW := by
    simp only [correction, denominator, normToken, signedSum_shift g z hg, dW, dB, s]
    ring
  apply sub_eq_zero.mp
  calc
    _ = (1+(g:R)) *
        ((correction q a Q (g*z)-correction q a Q z)*denominator a z -
          correction q a Q z*(denominator a (g*z)-denominator a z)) := by
      unfold numerator
      ring
    _ = ((g:R)^2-1)*(dW*denominator a z-correction q a Q z*dB) := by
      rw [hB, hW]
      ring
    _ = 0 := by rw [hg, sub_self, zero_mul]

theorem numerator_inactive (q : ℕ) (hq : q % 2 = 1) (a : R) (Q g z : Rˣ)
    (hQ : (Q:R) = q) (hg : (g:R) = 1) :
    numerator q a Q g z = euler a Q z := by
  rw [numerator, hg, one_add_one_eq_two, twice_correction q hq a Q z hQ]
  ring

theorem numerator_active (q : ℕ) (a : R) (Q g z : Rˣ) (hg : (g:R) = -1) :
    numerator q a Q g z = denominator a z := by
  rw [numerator, hg]
  ring

theorem orientation (q : ℕ) (a : R) (Q g z : Rˣ) :
    numerator q a Q g z⁻¹ = numerator q a Q g z ∧
    denominator a z⁻¹ = denominator a z := by
  have h : signedSum z⁻¹ = signedSum z := by
    simp only [signedSum, inv_inv, add_comm]
  constructor <;> simp only [numerator, correction, denominator, normToken, h]

end OriginalRCSupportWeightIdentity318
