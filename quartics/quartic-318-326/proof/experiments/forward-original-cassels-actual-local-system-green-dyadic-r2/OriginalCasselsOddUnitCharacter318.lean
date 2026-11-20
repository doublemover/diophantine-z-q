module
public import OriginalCasselsRamifiedResidue318
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public section

noncomputable section

namespace OriginalCasselsOddUnitCharacter318

open OriginalCasselsRamifiedResidue318 OriginalCasselsOddUnitSquare318
open OriginalCasselsOddTargetValuation318

variable {p : ℕ} [Fact p.Prime]

/-- The actual unit is a square in Qp iff its own nonzero residue is
a square, with both directions using the literal reduction map. -/
theorem unit_square_iff_residue (hp2 : p≠2) (A : ℤ_[p]) (hA : IsUnit A) :
    (∃ r : ℚ_[p], r≠0 ∧ (A:ℚ_[p])=r^2) ↔ IsSquare (PadicInt.toZMod A) := by
  constructor
  · rintro ⟨r,_,he⟩
    have hv := congrArg Padic.valuation he
    rw [actual_val_zero_of_unit A hA,Padic.valuation_pow] at hv
    have hr : r.valuation=0 := by omega
    obtain ⟨R,hR⟩ := actual_integral r hr.ge
    have hEq : A=R^2 := by
      apply PadicInt.ext
      simpa only [PadicInt.coe_pow,hR] using he
    refine ⟨PadicInt.toZMod R,?_⟩
    simpa only [map_pow,pow_two] using congrArg (PadicInt.toZMod (p:=p)) hEq
  · rintro ⟨s,h⟩
    let S : ℤ_[p] := s.val
    have hS : PadicInt.toZMod S=s := by simp only [S,map_natCast,ZMod.natCast_zmod_val]
    have hR : PadicInt.toZMod (S^2)=PadicInt.toZMod A := by rw [map_pow,hS,pow_two,←h]
    have hr₀ : PadicInt.toZMod A≠0 := (hA.map PadicInt.toZMod).ne_zero
    obtain ⟨t,ht,htA⟩ := unit_ratio_square_of_equal_residue hp2 A (S^2)
      (fun e => hr₀ (hR.symm.trans e)) hR.symm
    have hSq0 : (S:ℚ_[p])≠0 := by
      intro hc
      have hS0 : S=0 := PadicInt.ext hc
      have he : PadicInt.toZMod (S^2)=0 := by rw [hS0,zero_pow (by decide : (2:ℕ)≠0),map_zero]
      exact hr₀ (hR.symm.trans he)
    refine ⟨(S:ℚ_[p])*t,mul_ne_zero hSq0 ht,?_⟩
    simpa only [PadicInt.coe_pow,mul_pow] using htA

/-- Any two non-square unit residues give the same actual local
squareclass, proved directly through the square root of their product. -/
theorem unit_ratio_square_of_nonsquare (hp2 : p≠2) (A B : ℤ_[p])
    (hA : IsUnit A) (hB : IsUnit B)
    (ha : ¬IsSquare (PadicInt.toZMod A)) (hb : ¬IsSquare (PadicInt.toZMod B)) :
    ∃ r : ℚ_[p], r≠0 ∧ (A:ℚ_[p])=(B:ℚ_[p])*r^2 := by
  have hp : PadicInt.toZMod (A*B)≠0 := ((hA.mul hB).map PadicInt.toZMod).ne_zero
  have hχ : IsSquare (PadicInt.toZMod (A*B)) := by
    apply (quadraticChar_one_iff_isSquare hp).1
    rw [map_mul,map_mul,quadraticChar_neg_one_iff_not_isSquare.mpr ha,
      quadraticChar_neg_one_iff_not_isSquare.mpr hb]
    norm_num
  obtain ⟨r,hr,he⟩ := (unit_square_iff_residue hp2 (A*B) (hA.mul hB)).mpr hχ
  have hB0 : (B:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hB.ne_zero
  refine ⟨r/(B:ℚ_[p]),div_ne_zero hr hB0,?_⟩
  rw [div_pow,←he,PadicInt.coe_mul]
  field_simp [hB0] <;> ring

end OriginalCasselsOddUnitCharacter318

#print axioms OriginalCasselsOddUnitCharacter318.unit_square_iff_residue
