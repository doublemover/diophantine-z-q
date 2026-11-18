module
public import LegendreTernaryDescent318
public import LegendreGoodPrimeLocal318
public import LegendreSplitPrimeLocal318
public import Mathlib.Analysis.Real.Sqrt
import all LegendreTernaryDescent318
public section
namespace AuxiliaryGlobalBinary318
open LegendreTernaryDescent318

private theorem of_B {F : Type*} [Field F] (C t T Y : F)
    (h : C*T^2-6*Y^2=t) : Sol F (6*C) (C*t) := by
  apply of_affine (6*C) (C*t) (C*T) Y
  linear_combination C*h

/-- Assemble the second binary global representation from finite actual
local B-values, the one exceptional modular square and the real sign.
All other odd places are supplied by the checked good-prime theorem.
The exceptional square and support coverage remain explicit obligations
of the auxiliary-prime construction; no all-place or rational point premise
is hidden in this interface. -/
theorem rational_B_of_finite_locals (C t : ℤ) (hC : C≠0)
    (S : Finset ℕ) (h2 : 2∈S) (q : ℕ) (hqS : q∉S)
    (hqunit : ¬(q:ℤ)∣6*C) (hqsquare : IsSquare ((6*C:ℤ):ZMod q))
    (hsupport : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣(6*C)*(C*t) → p∈S ∨ p=q)
    (hfinite : ∀ p [Fact p.Prime], p∈S →
      ∃ T Y : ℚ_[p], (C:ℚ_[p])*T^2-6*Y^2=(t:ℚ_[p]))
    (hpos : (0:ℝ)<(t:ℝ)/(C:ℝ)) :
    ∃ T Y : ℚ, (C:ℚ)*T^2-6*Y^2=(t:ℚ) := by
  have hCR : (C:ℝ)≠0 := by exact_mod_cast hC
  have hCQ : (C:ℚ)≠0 := by exact_mod_cast hC
  have hq2 : q≠2 := by
    intro h
    exact hqS (by simpa [h] using h2)
  have hevery : Everywhere (6*C) (C*t) := by
    constructor
    · let T : ℝ := Real.sqrt ((t:ℝ)/(C:ℝ))
      have hb : (C:ℝ)*T^2-6*(0:ℝ)^2=(t:ℝ) := by
        dsimp only [T]
        rw [Real.sq_sqrt (le_of_lt hpos)]
        field_simp [hCR] <;> ring
      simpa only [Int.cast_mul,Int.cast_ofNat] using of_B (C:ℝ) (t:ℝ) T 0 hb
    · intro p hp
      by_cases hpS : p∈S
      · obtain ⟨T,Y,hb⟩ := hfinite p hpS
        simpa only [Int.cast_mul,Int.cast_ofNat] using
          of_B (C:ℚ_[p]) (t:ℚ_[p]) T Y hb
      · by_cases hpq : p=q
        · subst p
          obtain ⟨x,z,hz⟩ := LegendreSplitPrimeLocal318.represents_any
            q hq2 (6*C) (C*t) hqunit hqsquare
          exact of_affine ((6*C:ℤ):ℚ_[q]) ((C*t:ℤ):ℚ_[q]) z x hz
        · have hp2 : p≠2 := by
            intro h
            exact hpS (by simpa [h] using h2)
          have hout : ¬(p:ℤ)∣(6*C)*(C*t) := by
            intro hd
            rcases hsupport p hd with hs | hq
            · exact hpS hs
            · exact hpq hq
          have ha : ¬(p:ℤ)∣6*C := fun hd => hout (dvd_mul_of_dvd_left hd _)
          have hb : ¬(p:ℤ)∣C*t := fun hd => hout (dvd_mul_of_dvd_right hd _)
          obtain ⟨x,z,hz⟩ := LegendreGoodPrimeLocal318.represents_unit
            p hp2 (6*C) (C*t) ha hb
          exact of_affine ((6*C:ℤ):ℚ_[p]) ((C*t:ℤ):ℚ_[p]) z x hz
  have hglobal := rational_of_everywhere (6*C) (C*t) hevery
  have haQ : ((6*C:ℤ):ℚ)≠0 := by
    have ha : (6:ℤ)*C≠0 := mul_ne_zero (by norm_num) hC
    exact_mod_cast ha
  obtain ⟨z,x,hzx⟩ := to_affine haQ hglobal
  have hz : z^2-6*(C:ℚ)*x^2=(C:ℚ)*(t:ℚ) := by
    simpa only [Int.cast_mul,Int.cast_ofNat] using hzx
  refine ⟨z/(C:ℚ),x,?_⟩
  calc
    (C:ℚ)*(z/(C:ℚ))^2-6*x^2=(z^2-6*(C:ℚ)*x^2)/(C:ℚ) := by
      field_simp [hCQ] <;> ring
    _=((C:ℚ)*(t:ℚ))/(C:ℚ) := by rw [hz]
    _=(t:ℚ) := by field_simp [hCQ]

end AuxiliaryGlobalBinary318
