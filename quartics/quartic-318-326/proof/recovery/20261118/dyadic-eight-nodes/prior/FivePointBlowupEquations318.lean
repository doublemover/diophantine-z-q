module
public import OriginalPrimeThreeActualQuotient318
public import FourRootOrderSigns318
public section
noncomputable section
namespace FivePointBlowupEquations318
open Polynomial OriginalIntegerAffineModel318
abbrev twist := OriginalPrimeThreeActualQuotient318.twist
abbrev H := Order twist
@[expose] def r (i : Fin 4) : H := FourRootOrderSigns318.generator (coefficient twist) i

private theorem diff (i j : Fin 4) (a : ℤ)
    (h : coefficient twist i - coefficient twist j = (a : ℤ[X])) :
    r i ^ 2 - r j ^ 2 = (a : H) := by
  simp only [r, FourRootOrderSigns318.generator_square, ← map_sub, h, map_intCast]

/-- These are equations of the original four-root order. The retained
root r0 and all three colliding roots remain accounted for. -/
theorem literal :
    r 0 ^ 2 - r 1 ^ 2 = 32 ∧ r 2 ^ 2 - r 1 ^ 2 = -76800 ∧
    r 3 ^ 2 - r 1 ^ 2 = 375 := by
  constructor
  · have h := diff 0 1 (32) (by
      rw [OriginalPrimeThreeActualQuotient318.untwisted_coefficient,
        OriginalPrimeThreeActualQuotient318.untwisted_coefficient]
      norm_num [contacts] <;> ring)
    simpa using h
  constructor
  · have h := diff 2 1 (-76800) (by
      rw [OriginalPrimeThreeActualQuotient318.untwisted_coefficient,
        OriginalPrimeThreeActualQuotient318.untwisted_coefficient]
      norm_num [contacts] <;> ring)
    simpa using h
  · have h := diff 3 1 (375) (by
      rw [OriginalPrimeThreeActualQuotient318.untwisted_coefficient,
        OriginalPrimeThreeActualQuotient318.untwisted_coefficient]
      norm_num [contacts] <;> ring)
    simpa using h

/-- Uniform field equations, available in any residue field or in the
ambient characteristic-zero field. No denominator has yet been inverted. -/
theorem mapped {k : Type*} [Field k] (g : H →+* k) :
    g (r 0) ^ 2 - g (r 1) ^ 2 = 32 ∧
    g (r 2) ^ 2 - g (r 1) ^ 2 = -76800 ∧
    g (r 3) ^ 2 - g (r 1) ^ 2 = 375 := by
  exact ⟨by simpa using congrArg g literal.1, by simpa using congrArg g literal.2.1,
    by simpa using congrArg g literal.2.2⟩

/-- Coordinates of the 5-chart as fractions IN THE AMBIENT FIELD.
This does not invert 5 in the ratio chart or its special fibre. -/
theorem five_chart {k : Type*} [Field k] (g : H →+* k) (h5 : (5 : k) ≠ 0) :
    (g (r 2)/5)^2 - (g (r 1)/5)^2 = -3072 ∧
    (g (r 3)/5)^2 - (g (r 1)/5)^2 = 15 := by
  obtain ⟨_, hv, hw⟩ := mapped g
  constructor
  · rw [div_pow, div_pow, ← sub_div, div_eq_iff (pow_ne_zero 2 h5), hv]
    norm_num
  · rw [div_pow, div_pow, ← sub_div, div_eq_iff (pow_ne_zero 2 h5), hw]
    norm_num

/-- Homogeneous direction coverage is valid even when 5=0. If the
5- and first-root directions vanish, the other directions must also
vanish. Hence these two standard charts cover the Rees Proj. This lemma
is only the field-valued direction calculation, not the Proj join. -/
theorem directions {k : Type*} [Field k] (P U V W : k)
    (hv : V^2-U^2 = -3072*P^2) (hw : W^2-U^2 = 15*P^2)
    (hP : P = 0) (hU : U = 0) : V = 0 ∧ W = 0 := by
  subst P; subst U
  exact ⟨by simpa using hv, by simpa using hw⟩

end FivePointBlowupEquations318
