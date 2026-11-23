module
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Characteristic-zero function-field identities used on the original D=210
four-root model. No assertion of a fine integral PEL or metric comparison. -/
public section
namespace OriginalEllipticPairSections318

variable {K : Type*} [Field K]

@[expose] def contact (t : K) : K := t * (t - 32) * (t - 76832) * (t + 343)

/-- In the calibrated elliptic quotients, omegaInf/dT = 246960/product(r_i),
and omegaZero/dT = 630/(r1*r2*r3). This theorem checks both constants over
one original four-root field, before evaluating in any marked local frame. -/
theorem original_pair (t a b c d : K)
    (ha : a ^ 2 = -14 * t) (hb : b ^ 2 = -6 * (t - 32))
    (hc : c ^ 2 = 42 * (t - 76832)) (hd : d ^ 2 = -21 * (t + 343))
    (habcd : a * b * c * d ≠ 0) (hP : contact t ≠ 0) :
    (246960 / (a * b * c * d)) ^ 2 = -823200 / contact t ∧
    (630 / (b * c * d)) ^ 2 = 75 * t / contact t := by
  have hprod : (a * b * c * d) ^ 2 = -74088 * contact t := by
    simp only [mul_pow, ha, hb, hc, hd, contact]
    ring
  have htriple : (b * c * d) ^ 2 = 5292 * (t - 32) * (t - 76832) * (t + 343) := by
    simp only [mul_pow, hb, hc, hd]
    ring
  have h3 : b * c * d ≠ 0 := by
    intro h
    apply habcd
    calc
      a * b * c * d = a * (b * c * d) := by ring
      _ = 0 := by rw [h, mul_zero]
  constructor
  · rw [div_pow]
    apply (div_eq_div_iff (pow_ne_zero 2 habcd) hP).2
    rw [hprod]
    ring
  · rw [div_pow]
    apply (div_eq_div_iff (pow_ne_zero 2 h3) hP).2
    rw [htriple, contact]
    ring

/-- Tangent duplication with the *signed* completed ordinate Y=-a*b*c.
The three entries at x are x-e_i = a_i². All outputs in the conjunction
can be checked without inversion or a non-torsion side condition. -/
theorem signed_half_chord (x a b c : K) :
    let e₁ := x - a ^ 2
    let e₂ := x - b ^ 2
    let e₃ := x - c ^ 2
    let s := a + b + c
    let p := a * b + a * c + b * c
    let y := -(a * b * c)
    let xh := x + p
    let yh := -y - s * p
    yh ^ 2 = (xh - e₁) * (xh - e₂) * (xh - e₃) ∧
    (-s) * (2 * yh) =
      (xh - e₁) * (xh - e₂) + (xh - e₁) * (xh - e₃) + (xh - e₂) * (xh - e₃) ∧
    (-s) ^ 2 + e₁ + e₂ + e₃ - 2 * xh = x ∧
    (-s) * (xh - x) - yh = y := by
  dsimp only
  exact ⟨by ring, by ring, by ring, by ring⟩

variable [CharZero K]

private theorem root_jet {R : Type*} [CommRing R] [Algebra R K]
    (D : Derivation R K K) (x a : K) (e : R)
    (he : a ^ 2 = x - algebraMap R K e) (ha : a ≠ 0) :
    D a = D x / (2 * a) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).2
  have h := congrArg D he
  rw [pow_two, D.leibniz, map_sub, D.map_algebraMap, sub_zero] at h
  change a * D a + a * D a = D x at h
  calc
    D a * (2 * a) = a * D a + a * D a := by ring
    _ = D x := h

/-- The coefficient of the actual pullback of the half-point differential
in any derivation frame. The hypotheses concern *functions* and constant
branch coordinates, not their values at a number-field point. Clearing gives
(2Y) d(xh) = yh dx, i.e. d(xh)/(2yh)=dx/(4Y) on the ordinary generic open. -/
theorem signed_half_differential {R : Type*} [CommRing R] [Algebra R K]
    (D : Derivation R K K) (x a b c : K) (e₁ e₂ e₃ : R)
    (h₁ : a ^ 2 = x - algebraMap R K e₁)
    (h₂ : b ^ 2 = x - algebraMap R K e₂)
    (h₃ : c ^ 2 = x - algebraMap R K e₃)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (2 * -(a * b * c)) * D (x + (a * b + a * c + b * c)) =
      (a * b * c - (a + b + c) * (a * b + a * c + b * c)) * D x := by
  simp only [map_add, D.leibniz, smul_eq_mul, root_jet D x a e₁ h₁ ha,
    root_jet D x b e₂ h₂ hb, root_jet D x c e₃ h₃ hc]
  field_simp [ha, hb, hc]
  ring

end OriginalEllipticPairSections318

#print axioms OriginalEllipticPairSections318.original_pair
#print axioms OriginalEllipticPairSections318.signed_half_chord
#print axioms OriginalEllipticPairSections318.signed_half_differential
