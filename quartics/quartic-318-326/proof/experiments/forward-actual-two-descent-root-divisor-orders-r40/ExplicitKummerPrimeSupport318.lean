module
public import ExplicitPositiveKummer318
public import Mathlib.Data.ZMod.Basic
public section
namespace ExplicitKummerPrimeSupport318

/-- The two auxiliary factors force beta to be a residue square at every
prime dividing the constructed twist. This is a constraint on its support,
not freedom to prescribe arbitrary auxiliary primes. -/
lemma residue_square {F : Type*} [Field F] (β t : F)
    (h : β*(β-t^2)*(β-9*t^2)=0) : IsSquare β := by
  rcases mul_eq_zero.mp h with hleft | hright
  · rcases mul_eq_zero.mp hleft with hbeta | hfirst
    · exact ⟨0, by simpa using hbeta⟩
    · exact ⟨t, by simpa only [pow_two] using sub_eq_zero.mp hfirst⟩
  · refine ⟨3*t, ?_⟩
    calc
      β = 9*t^2 := sub_eq_zero.mp hright
      _ = (3*t)*(3*t) := by ring

/-- Actual prime divisibility, rather than an assumed residue-square input. -/
theorem square_at_parameter_prime (β t : ℤ) (p : ℕ) [Fact p.Prime]
    (hp : (p:ℤ) ∣ β*(β-t^2)*(β-9*t^2)) : IsSquare (β : ZMod p) := by
  apply residue_square (β : ZMod p) (t : ZMod p)
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (β*(β-t^2)*(β-9*t^2)) p).mpr hp
  simpa only [Int.cast_mul,Int.cast_sub,Int.cast_pow,Int.cast_ofNat] using h

/-- The integer expression is exactly the previously constructed rational
twist parameter, not a new surrogate polynomial. -/
lemma integer_parameter (β t : ℤ) :
    ExplicitPositiveKummer318.parameter (β:ℚ) (t:ℚ)=
      ((β*(β-t^2)*(β-9*t^2):ℤ):ℚ) := by
  simp only [ExplicitPositiveKummer318.parameter,Int.cast_mul,Int.cast_sub,
    Int.cast_pow,Int.cast_ofNat]

end ExplicitKummerPrimeSupport318
