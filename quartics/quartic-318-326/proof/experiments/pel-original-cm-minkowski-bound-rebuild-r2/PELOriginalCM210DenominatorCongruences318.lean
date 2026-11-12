module
public import PELOriginalCM210IntegralTraceData318
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
public section
noncomputable section
namespace PELOriginalCM210DenominatorCongruences318
lemma mod8_obstruction : ∀t u:ZMod 8,210*t^2+u^2=0 →
    ZMod.castHom (by decide : 2∣8) (ZMod 2) t=0 ∧
    ZMod.castHom (by decide : 4∣8) (ZMod 4) u=0 := by decide
lemma odd_obstruction (p:ℕ) (hp:p=3 ∨ p=5 ∨ p=7) :
    ∀t u:ZMod p,210*t^2+u^2=0 → u=0 := by
  rcases hp with rfl|rfl|rfl <;> decide
lemma denominators (T U N:ℤ) (h:210*T^2+U^2=840*N) : 2∣T ∧ 420∣U := by
  have h8 : 210*(T:ZMod 8)^2+(U:ZMod 8)^2=0 := by
    have hh := congrArg (Int.castRingHom (ZMod 8)) h
    norm_num at hh ⊢ <;> exact hh
  have hh := mod8_obstruction (T:ZMod 8) (U:ZMod 8) h8
  have ht : 2∣T := (ZMod.intCast_zmod_eq_zero_iff_dvd T 2).mp (by simpa using hh.1)
  have hu4 : 4∣U := (ZMod.intCast_zmod_eq_zero_iff_dvd U 4).mp (by simpa using hh.2)
  have odd (p:ℕ) (hp:p=3 ∨ p=5 ∨ p=7) : (p:ℤ)∣U := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd U p).mp
    apply odd_obstruction p hp (T:ZMod p) (U:ZMod p)
    have hh := congrArg (Int.castRingHom (ZMod p)) h
    rcases hp with rfl|rfl|rfl <;> norm_num at hh ⊢ <;> exact hh
  have hu3 : (3:ℤ)∣U := odd 3 (Or.inl rfl)
  have hu5 : (5:ℤ)∣U := odd 5 (Or.inr (Or.inl rfl))
  have hu7 : (7:ℤ)∣U := odd 7 (Or.inr (Or.inr rfl))
  have hu12 : (12:ℤ)∣U :=
    (show IsCoprime (4:ℤ) 3 from ⟨1,-1,by norm_num⟩).mul_dvd hu4 hu3
  have hu60 : (60:ℤ)∣U :=
    (show IsCoprime (12:ℤ) 5 from ⟨-2,5,by norm_num⟩).mul_dvd hu12 hu5
  exact ⟨ht,(show IsCoprime (60:ℤ) 7 from ⟨2,-17,by norm_num⟩).mul_dvd hu60 hu7⟩

end PELOriginalCM210DenominatorCongruences318
