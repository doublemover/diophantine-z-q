module
public import ScalarSmallPrimePreparation318
public import Mathlib.NumberTheory.Padics.Hensel
public section
noncomputable section
namespace ScalarLocalSquares318
open Polynomial ScalarForwardWitness318 ScalarPolePreparation318 ScalarSmallPrimePreparation318
set_option maxHeartbeats 0
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Genuine Hensel production, including the ramified derivative at2. -/
lemma square_of_near_square (p : ℕ) [Fact p.Prime] (u v : ℤ_[p])
    (hnear : ‖u^2-v‖< ‖2*u‖^2) : IsSquare v := by
  let F : Polynomial ℤ_[p] := X^2-C v
  have hn : ‖F.aeval u‖< ‖F.derivative.aeval u‖^2 := by
    simpa [F] using hnear
  obtain ⟨z,hz,_⟩ := hensels_lemma hn
  have he : z^2=v := sub_eq_zero.mp (by simpa [F] using hz)
  exact ⟨z,by simpa only [pow_two] using he.symm⟩

lemma square_two_shape (k : ℤ) : IsSquare ((1+8*k:ℤ):ℤ_[2]) := by
  apply square_of_near_square 2 1
  have he : (1:ℤ_[2])^2-((1+8*k:ℤ):ℤ_[2])= -(2:ℤ_[2])^3*(k:ℤ_[2]) := by
    push_cast
    ring
  have hb : ‖(k:ℤ_[2])‖≤1 := PadicInt.norm_le_one _
  simp only [he,norm_mul,norm_neg,norm_pow,mul_one,PadicInt.norm_p]
  norm_num
  nlinarith

lemma square_three_shape (k : ℤ) : IsSquare ((1+3*k:ℤ):ℤ_[3]) := by
  apply square_of_near_square 3 1
  have he : (1:ℤ_[3])^2-((1+3*k:ℤ):ℤ_[3])= -(3:ℤ_[3])*(k:ℤ_[3]) := by
    push_cast
    ring
  have hd : ‖(2:ℤ_[3])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hb : ‖(k:ℤ_[3])‖≤1 := PadicInt.norm_le_one _
  rw [he,norm_mul,norm_neg,mul_one,PadicInt.norm_p,hd]
  norm_num
  nlinarith

lemma square_seventeen_shape (k : ℤ) : IsSquare ((8+17*k:ℤ):ℤ_[17]) := by
  apply square_of_near_square 17 5
  have he : (5:ℤ_[17])^2-((8+17*k:ℤ):ℤ_[17])=
      (17:ℤ_[17])*(1-(k:ℤ_[17])) := by
    push_cast
    ring
  have hd : ‖(10:ℤ_[17])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hb : ‖1-(k:ℤ_[17])‖≤1 := PadicInt.norm_le_one _
  rw [he,norm_mul,PadicInt.norm_p]
  norm_num only [show (2:ℤ_[17])*5=10 by norm_num,hd,one_pow]
  norm_num
  nlinarith

lemma rational_square_of_integral (p : ℕ) [Fact p.Prime] (a : ℤ)
    (h : IsSquare (a:ℤ_[p])) : IsSquare ((a:ℚ):ℚ_[p]) := by
  obtain ⟨z,hz⟩ := h
  refine ⟨(z:ℚ_[p]),?_⟩
  have he := congrArg (fun t : ℤ_[p] => (t:ℚ_[p])) hz
  simpa only [PadicInt.coe_mul,PadicInt.coe_intCast,Rat.cast_intCast] using he

/-- The actual source scalar multiplier is a square at each required small
prime. The roots are produced by Hensel, not supplied as new hypotheses. -/
theorem actual_multiplier_squares (a : ℤ) :
    IsSquare ((114444*inputR (a:ℚ):ℚ):ℚ_[2]) ∧
    IsSquare ((114444*inputR (a:ℚ):ℚ):ℚ_[3]) ∧
    IsSquare ((114444*inputR (a:ℚ):ℚ):ℚ_[17]) := by
  obtain ⟨⟨k₂,h₂⟩,⟨k₃,h₃⟩,⟨k₁₇,h₁₇⟩⟩ := integerA_shapes a
  have hcast : 114444*inputR (a:ℚ)=((114444*integerR a:ℤ):ℚ) := by
    rw [Int.cast_mul,integerR_cast]
    norm_num
  rw [hcast]
  refine ⟨?_,?_,?_⟩
  · apply rational_square_of_integral
    rw [h₂,Int.cast_mul]
    exact (show IsSquare ((16:ℤ):ℤ_[2]) from ⟨4,by norm_num⟩).mul (square_two_shape k₂)
  · apply rational_square_of_integral
    rw [h₃,Int.cast_mul]
    exact (show IsSquare ((9:ℤ):ℤ_[3]) from ⟨3,by norm_num⟩).mul (square_three_shape k₃)
  · apply rational_square_of_integral
    rw [h₁₇,Int.cast_mul]
    exact (show IsSquare ((289:ℤ):ℤ_[17]) from ⟨17,by norm_num⟩).mul (square_seventeen_shape k₁₇)

/-- Local squareness survives the exact scalar normalization for any actual
common point. Only the valuation depths and reduced-denominator condition
require later local index preparation. -/
theorem actual_pole_squares (w : CircuitReplay.Assignment) (n a : ℤ) (hin : w 0=(a:ℚ)) :
    IsSquare ((poleInput w n:ℚ):ℚ_[2]) ∧
    IsSquare ((poleInput w n:ℚ):ℚ_[3]) ∧
    IsSquare ((poleInput w n:ℚ):ℚ_[17]) := by
  obtain ⟨h₂,h₃,h₁₇⟩ := actual_multiplier_squares a
  rw [←hin] at h₂ h₃ h₁₇
  exact ⟨normalized_square (Rat.castHom ℚ_[2]) _ _ h₂,
    normalized_square (Rat.castHom ℚ_[3]) _ _ h₃,
    normalized_square (Rat.castHom ℚ_[17]) _ _ h₁₇⟩

end ScalarLocalSquares318
