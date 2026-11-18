module
public import FivePointBlowupEquations318
public section
noncomputable section
namespace SevenPointBlowupEquations318
open FivePointBlowupEquations318

/-- Reindex the actual same roots for the characteristic-seven cluster:
u=r0, v=r2, w=r3; the retained root is now r1, NOT r0. -/
theorem literal_seven :
    r 2^2-r 0^2 = -32*(7:H)^4 ∧
    r 3^2-r 0^2 = (7:H)^3 ∧
    r 1^2-r 0^2 = -32 := by
  obtain ⟨h0,h2,h3⟩ := literal
  constructor
  · linear_combination h2 - h0
  constructor
  · linear_combination h3 - h0
  · linear_combination -h0

/-- Successive W-chart equations after the FIRST 7-chart. The only
inversion below is in a FIELD and never asserts a chart denominator unit. -/
theorem second_W_equations {k : Type*} [Field k] (U V W : k) (hW : W ≠ 0)
    (h0 : W^2-U^2 = 7) (h1 : V^2-U^2 = -32*(7:k)^2) :
    W^2*(1-(U/W)^2) = 7 ∧
    (V/W)^2-(U/W)^2 = -32*W^2*(1-(U/W)^2)^2 := by
  have hh : W^2*(1-(U/W)^2) = 7 := by
    calc
      _ = W^2-U^2 := by field_simp [hW] <;> ring
      _ = _ := h0
  refine ⟨hh, ?_⟩
  calc
    _ = (V^2-U^2)/W^2 := by rw [sub_div, div_pow, div_pow]
    _ = -32*(W^2*(1-(U/W)^2))^2/W^2 := by rw [h1, hh]
    _ = _ := by field_simp [hW] <;> ring

/-- Literal tangent conic of the third blowup. Euler's identity allows
dehomogenization on any of its three standard projective coordinate charts. -/
theorem conic_euler {k : Type*} [CommRing k] (w a c : k) :
    w*(64*w)+a*(-2*a)+c*(2*c) = 2*(c^2-a^2+32*w^2) := by ring

/-- No nonzero direction has all three gradient entries zero. 2≠0
suffices (including the genuine characteristic-seven residue fields). -/
theorem conic_gradient {k : Type*} [Field k] (h2 : (2:k) ≠ 0) (w a c : k)
    (hn : w ≠ 0 ∨ a ≠ 0 ∨ c ≠ 0) :
    ¬ (64*w=0 ∧ -2*a=0 ∧ 2*c=0) := by
  have h64 : (64:k) ≠ 0 := by
    convert (pow_ne_zero 6 h2) using 1 <;> norm_num
  rintro ⟨hw,ha,hc⟩
  rcases hn with hw' | ha' | hc'
  · exact (mul_ne_zero h64 hw') hw
  · exact (mul_ne_zero (neg_ne_zero.mpr h2) ha') ha
  · exact (mul_ne_zero h2 hc') hc

end SevenPointBlowupEquations318
