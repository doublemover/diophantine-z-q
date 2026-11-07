module
public import Height13RealLog
public import Mathlib.Data.ZMod.Basic
public section

/-! Algebra used after the actual theta coefficient comparison and integer
    divisibility have been established. No theta modularity is axiomatized here. -/
namespace OddCoefficientReading

variable {O k : Type*} [CommRing O] [IsDomain O] [Field k] [CharP k 2]

/-- Every phase allowed by the source disappears in the residue field. -/
theorem phase_reduces_one (rho : O →+* k) (zeta : O) (e : ℕ)
    (hz : zeta ^ (2 ^ e) = 1) : rho zeta = 1 := by
  have hz' : (rho zeta) ^ (2 ^ e) = 1 := by
    simpa only [map_pow, map_one] using congrArg rho hz
  have hnil : (rho zeta - 1) ^ (2 ^ e) = 0 := by
    rw [sub_pow_char_pow, hz', one_pow, sub_self]
  exact eq_of_sub_eq_zero ((pow_eq_zero_iff (by positivity)).mp hnil)

/-- Integer coefficients reduce to the prime field, even when the residue
    field is larger and the coefficient valuation ring is ramified. -/
theorem integer_residue_binary (j : ℤ) :
    (j : k) = 0 ∨ (j : k) = 1 := by
  have hj : j = 2 * (j / 2) + j % 2 := by omega
  have hred : (j : k) = ((j % 2 : ℤ) : k) := by
    calc
      (j : k) = ((2 * (j / 2) + j % 2 : ℤ) : k) := congrArg Int.cast hj
      _ = ((j % 2 : ℤ) : k) := by
        push_cast
        rw [show (2 : k) = 0 from CharP.cast_eq_zero k 2]
        simp
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left; simpa [h] using hred
  · right; simpa [h] using hred

/-- Cancel an actual power of the integer two before reducing. Precision is
    stated additively: M = n+1+t, so one full integer factor two remains. -/
theorem normalized_integer_congruence (rho : O →+* k)
    (htwo : (2 : O) ≠ 0) (a b zeta err : O) (j : ℤ) (n t e : ℕ)
    (hz : zeta ^ (2 ^ e) = 1)
    (ha : a = 2 ^ n * b)
    (hcomp : a = zeta * (2 ^ n * (j : O)) + 2 ^ (n + 1 + t) * err) :
    rho b = (j : k) := by
  have hp : (2 : O) ^ n ≠ 0 := pow_ne_zero _ htwo
  have hc : b = zeta * (j : O) + 2 ^ (1 + t) * err := by
    apply mul_left_cancel₀ hp
    rw [← ha, hcomp]
    rw [show n + 1 + t = n + (1 + t) by omega, pow_add]
    ring
  rw [hc, map_add, map_mul, phase_reduces_one rho zeta e hz, one_mul,
    map_mul, map_pow, map_ofNat, map_intCast]
  rw [show (2 : k) = 0 from CharP.cast_eq_zero k 2,
    zero_pow (by omega : 1 + t ≠ 0)]
  simp

/-- The needed integer quotient is itself forced by the actual coefficient
    divisibility. This works in ramified rings: it never identifies 2O with
    the maximal ideal, nor divides a reduced identity by two. -/
theorem integer_divisibility_from_coefficient (rho : O →+* k)
    (htwo : (2 : O) ≠ 0) (zeta : O) (e : ℕ)
    (hz : zeta ^ (2 ^ e) = 1) (n : ℕ) :
    ∀ (b err : O) (q : ℤ) (t : ℕ),
      2 ^ n * b = zeta * (q : O) + 2 ^ (n+1+t) * err →
      (2 : ℤ) ^ n ∣ q := by
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro b err q t hc
    have hr := congrArg rho hc
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    simp only [map_mul, map_add, map_pow, map_ofNat, map_intCast] at hr
    rw [phase_reduces_one rho zeta e hz, h2] at hr
    have hqzero : (q : k) = 0 := by simpa using hr.symm
    have hqeven : (2 : ℤ) ∣ q := (CharP.intCast_eq_zero_iff k 2 q).mp hqzero
    obtain ⟨q1, hq⟩ := hqeven
    have hdiv : (2 : O) ^ n * b = zeta * (q1 : O) + 2 ^ (n+1+t) * err := by
      apply mul_left_cancel₀ htwo
      calc
        2 * (2 ^ n * b) = 2 ^ (n+1) * b := by rw [pow_succ']; ring
        _ = zeta * (q : O) + 2 ^ (n+1+1+t) * err := hc
        _ = 2 * (zeta * (q1 : O) + 2 ^ (n+1+t) * err) := by
          rw [hq]
          push_cast
          rw [show n+1+1+t = (n+1+t)+1 by omega, pow_succ]
          ring
    obtain ⟨j, hj⟩ := ih b err q1 t hdiv
    use j
    rw [hq, hj, pow_succ']
    ring

/-- Exact finite-stage binary reading from the raw phased integer q,
    with the integer quotient derived rather than postulated. -/
theorem finite_stage_binary_reading (rho : O →+* k)
    (htwo : (2 : O) ≠ 0) (b zeta err : O) (q : ℤ) (n t e : ℕ)
    (hz : zeta ^ (2 ^ e) = 1)
    (hc : 2 ^ n * b = zeta * (q : O) + 2 ^ (n+1+t) * err) :
    ∃ j : ℤ, q = 2 ^ n * j ∧ rho b = (j : k) ∧
      (rho b = 0 ∨ rho b = 1) := by
  obtain ⟨j,hj⟩ := integer_divisibility_from_coefficient rho htwo zeta e hz n b err q t hc
  refine ⟨j, hj, ?_, ?_⟩
  · apply normalized_integer_congruence rho htwo (2^n*b) b zeta err j n t e hz rfl
    simpa only [hj, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hc
  · have hread : rho b = (j : k) := by
      apply normalized_integer_congruence rho htwo (2^n*b) b zeta err j n t e hz rfl
      simpa only [hj, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hc
    rw [hread]
    exact integer_residue_binary j

/-- Source comparison plus a protected actual integer division produces a
    binary coefficient, not merely an arbitrary residue-field coefficient. -/
theorem normalized_coefficient_binary (rho : O →+* k)
    (htwo : (2 : O) ≠ 0) (a b zeta err : O) (j : ℤ) (n t e : ℕ)
    (hz : zeta ^ (2 ^ e) = 1)
    (ha : a = 2 ^ n * b)
    (hcomp : a = zeta * (2 ^ n * (j : O)) + 2 ^ (n + 1 + t) * err) :
    rho b = 0 ∨ rho b = 1 := by
  rw [normalized_integer_congruence rho htwo a b zeta err j n t e hz ha hcomp]
  exact integer_residue_binary j

/-- Negative normalized depths cannot produce a unit: normalizing then
    multiplies an integral coefficient by a positive power of two. -/
theorem negative_depth_reading (rho : O →+* k) (a : O) (n : ℕ) :
    rho (2 ^ (n+1) * a) = 0 := by
  rw [map_mul, map_pow, map_ofNat,
    show (2 : k) = 0 from CharP.cast_eq_zero k 2,
    zero_pow (by omega : n+1 ≠ 0), zero_mul]

/-- The actual precision budget in O.9--O.11 protects both divisions. -/
theorem stage_precision (delta W U M R : ℤ) (hU : U ≤ W)
    (hR : 2 ≤ R) (hM : max 0 (delta + W) + R ≤ M) :
    1 ≤ M - (delta + U) - 1 := by omega

#print axioms phase_reduces_one
#print axioms integer_residue_binary
#print axioms normalized_integer_congruence
#print axioms integer_divisibility_from_coefficient
#print axioms finite_stage_binary_reading
#print axioms normalized_coefficient_binary
#print axioms negative_depth_reading
#print axioms stage_precision
end OddCoefficientReading
