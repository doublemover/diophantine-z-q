module
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Tactic
public section
namespace AuxiliarySignedReciprocity318
open Nat ZMod

/-- Signed reciprocity for the actual coefficient residue. In the negative
case the numerator sign cancels the quadratic-reciprocity sign. -/
theorem signed_reciprocity (C : ℤ) (q : ℕ)
    (hC : C%4=1) (hq : Odd q) :
    jacobiSym C q=jacobiSym (q:ℤ) C.natAbs := by
  rcases Int.natAbs_eq C with he | he
  · have hN : C.natAbs%4=1 := by
      have hh : (C.natAbs:ℤ)%4=1 := by rw [←he]; exact hC
      exact_mod_cast hh
    calc
      jacobiSym C q=jacobiSym (C.natAbs:ℤ) q := congrArg (fun z => jacobiSym z q) he
      _=jacobiSym (q:ℤ) C.natAbs := jacobiSym.quadratic_reciprocity_one_mod_four hN hq
  · have hN : C.natAbs%4=3 := by
      have hh : (-(C.natAbs:ℤ))%4=1 := by rw [←he]; exact hC
      have hh' : (C.natAbs:ℤ)%4=3 := by omega
      exact_mod_cast hh'
    have hNodd : Odd C.natAbs := Nat.odd_iff.mpr (by omega)
    calc
      jacobiSym C q=jacobiSym (-(C.natAbs:ℤ)) q := congrArg (fun z => jacobiSym z q) he
      _=χ₄ q*jacobiSym (C.natAbs:ℤ) q := jacobiSym.neg _ hq
      _=jacobiSym (q:ℤ) C.natAbs := by
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with hq1 | hq3
        · rw [χ₄_nat_one_mod_four hq1,one_mul,
            jacobiSym.quadratic_reciprocity_one_mod_four' hNodd hq1]
        · rw [χ₄_nat_three_mod_four hq3,
            jacobiSym.quadratic_reciprocity_three_mod_four hN hq3]
          <;> ring

/-- Once the actual finite Jacobi product is proved to be1 and q splits6,
the coefficient6C is a square modulo q. The finite product and auxiliary
prime selection remain separate obligations, not conclusions of this lemma. -/
theorem square_six_coefficient_of_product (C : ℤ) (q : ℕ) [Fact q.Prime]
    (hC : C%24=1) (hq : Odd q)
    (hsix : jacobiSym 6 q=1) (hproduct : jacobiSym (q:ℤ) C.natAbs=1) :
    IsSquare ((6*C:ℤ):ZMod q) := by
  apply ZMod.isSquare_of_jacobiSym_eq_one
  rw [jacobiSym.mul_left,signed_reciprocity C q (by omega) hq,hsix,hproduct]
  <;> norm_num

end AuxiliarySignedReciprocity318
