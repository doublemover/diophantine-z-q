module
public import RCIntegralGroupRingCongruence318
public import Mathlib.NumberTheory.Padics.RingHoms
public section
noncomputable section
namespace RCTwoAdicBinaryCongruence318
open scoped BigOperators
open RCSignCharacterCongruence318

/-- Binary congruences for arbitrary actual 2-adic coefficients of the
elementary Boolean group ring. Equality is in the native quotient modulo
2^M. The coefficient reduction, bit polynomials and degree bounds are all
constructed in the preceding proofs; none is a hypothesis here. -/
theorem exists_nonzero_character (b r M : ℕ)
    (z : Fin r → Cube b → ℤ_[2])
    (hsize : r * (2 ^ M - 1) < b) :
    ∃ x : Cube b, x ≠ 0 ∧ ∀ i,
      PadicInt.toZModPow M (∑ g, z i g * (sign g x : ℤ_[2])) =
        PadicInt.toZModPow M (∑ g, z i g) := by
  classical
  let φ : ℤ_[2] →+* ZMod (2 ^ M) := PadicInt.toZModPow M
  let c : Fin r → Cube b → ℤ := fun i g => (φ (z i g)).val
  have hc (i : Fin r) (g : Cube b) : (c i g : ZMod (2 ^ M)) = φ (z i g) := by
    simp only [c, Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨x,hx,h⟩ := RCIntegralGroupRingCongruence318.exists_nonzero_integral_congruence
    b r M (Finset.univ : Finset (Cube b)).toList c hsize
  refine ⟨x,hx,fun i => ?_⟩
  have hi : (2 ^ M : ℤ) ∣
      (∑ g, c i g * sign g x) - ∑ g, c i g := by
    simpa only [Finset.sum_map_toList] using h i
  have hz : (((∑ g, c i g * sign g x) - ∑ g, c i g : ℤ) : ZMod (2 ^ M)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact_mod_cast hi
  have heq : (∑ g, φ (z i g) * (sign g x : ZMod (2 ^ M))) = ∑ g, φ (z i g) := by
    simpa only [Int.cast_sub, Int.cast_sum, Int.cast_mul, hc, sub_eq_zero] using hz
  simpa only [map_sum, map_mul, map_intCast] using heq

end RCTwoAdicBinaryCongruence318
