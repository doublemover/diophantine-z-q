module
public import OriginalCasselsOddUnitCharacter318
public import ActualTwoDescentSquareClassQuotient318
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTOddSquareclassBasis318

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentLocalValuationTools318
open OriginalCasselsOddUnitCharacter318 OriginalCasselsOddTargetValuation318
open OriginalCasselsRamifiedResidue318

variable {p : ℕ} [Fact p.Prime]

private def bitValue (a : ℚ_[p]) (b : Bool) : ℚ_[p] := if b then a else 1

private theorem bitValue_ne (a : ℚ_[p]) (ha : a≠0) (b : Bool) : bitValue a b≠0 := by
  cases b <;> simp [bitValue,ha]

private theorem bitValue_val (a : ℚ_[p]) (b : Bool) :
    (bitValue a b).valuation=if b then a.valuation else 0 := by
  cases b <;> simp [bitValue,Padic.valuation_one]

private def bitClass (a : ℚ_[p]) (ha : a≠0) (b : Bool) : SquareClass ℚ_[p] :=
  classOf (bitValue a b) (bitValue_ne a ha b)

private theorem bitClass_false (a : ℚ_[p]) (ha : a≠0) : bitClass a ha false=1 := by
  exact class_of_one

private theorem bitClass_true (a : ℚ_[p]) (ha : a≠0) : bitClass a ha true=classOf a ha := rfl

/-- Same actual squareclass representatives 1,b,a,ab from a value-one
uniformizer a and a nonsquare integral unit b, not a picked abstract basis. -/
def actualBasis (a : ℚ_[p]) (ha : a≠0) (B : ℤ_[p]) (hB : IsUnit B)
    (i : Bool × Bool) : SquareClass ℚ_[p] :=
  bitClass a ha i.1 * bitClass (B:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hB.ne_zero) i.2

theorem basis_values (a : ℚ_[p]) (ha : a≠0) (B : ℤ_[p]) (hB : IsUnit B) :
    actualBasis a ha B hB (false,false)=1 ∧
    actualBasis a ha B hB (false,true)=classOf (B:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hB.ne_zero) ∧
    actualBasis a ha B hB (true,false)=classOf a ha ∧
    actualBasis a ha B hB (true,true)=classOf (a*(B:ℚ_[p]))
      (mul_ne_zero ha (PadicInt.coe_ne_zero.mpr hB.ne_zero)) := by
  simp [actualBasis,bitClass_true,bitClass_false,class_of_mul]

private theorem unit_class_covers (hp2 : p≠2) (A B : ℤ_[p]) (hA : IsUnit A)
    (hB : IsUnit B) (hBns : ¬IsSquare (PadicInt.toZMod B)) :
    ∃ b : Bool, classOf (A:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hA.ne_zero) =
      bitClass (B:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hB.ne_zero) b := by
  by_cases hs : IsSquare (PadicInt.toZMod A)
  · obtain ⟨r,hr,he⟩ := (unit_square_iff_residue hp2 A hA).mpr hs
    refine ⟨false,?_⟩
    rw [bitClass_false,←class_of_one]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,by simpa only [one_mul] using he⟩
  · obtain ⟨r,hr,he⟩ := unit_ratio_square_of_nonsquare hp2 A B hA hB hs hBns
    refine ⟨true,?_⟩
    rw [bitClass_true]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,he⟩

theorem actualBasis_surjective (hp2 : p≠2) (a : ℚ_[p]) (ha : a≠0) (haV : a.valuation=1)
    (B : ℤ_[p]) (hB : IsUnit B) (hBns : ¬IsSquare (PadicInt.toZMod B)) :
    Function.Surjective (actualBasis a ha B hB) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro u
  let x : ℚ_[p] := ↑u
  have hx : x≠0 := u.ne_zero
  let x0 := x / a^x.valuation
  have haPow : a^x.valuation≠0 := zpow_ne_zero _ ha
  have hx0 : x0≠0 := div_ne_zero hx haPow
  have hxV : x0.valuation=0 := by
    change (x/a^x.valuation).valuation=0
    rw [actual_valuation_div _ _ hx haPow,Padic.valuation_zpow,haV,mul_one,sub_self]
  obtain ⟨U,hU⟩ := actual_integral x0 hxV.ge
  have hUnit : IsUnit U := PadicInt.isUnit_iff.mpr
    (by rw [hU]; exact actual_norm_one_of_valuation_zero x0 hx0 hxV)
  have hU0 : (U:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hUnit.ne_zero
  let k := x.valuation/2
  let I : Bool := if x.valuation%2=0 then false else true
  have hPow : a^x.valuation = bitValue a I * (a^k)^2 := by
    by_cases h : x.valuation%2=0
    · have he : x.valuation=k+k := by dsimp [k]; omega
      simp [I,h,bitValue]
      rw [he,zpow_add₀ ha,pow_two]
    · have he : x.valuation=k+k+1 := by dsimp [k]; omega
      simp [I,h,bitValue]
      rw [he,zpow_add₀ ha,zpow_add₀ ha,zpow_one,pow_two]
      ac_rfl
  have hFactor : x=(bitValue a I * (U:ℚ_[p]))*(a^k)^2 := calc
    x = x0*(a^x.valuation) := by
      exact (div_mul_cancel₀ x haPow).symm
    _ = _ := by rw [←hU,hPow]; ac_rfl
  have hAu := bitValue_ne a ha I
  have hcl : classOf x hx = bitClass a ha I * classOf (U:ℚ_[p]) hU0 := by
    unfold bitClass
    rw [←class_of_mul]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨a^k,zpow_ne_zero _ ha,hFactor⟩
  obtain ⟨J,hJ⟩ := unit_class_covers hp2 U B hUnit hB hBns
  refine ⟨(I,J),?_⟩
  have hmk : Units.mk0 x hx=u := by ext; rfl
  change bitClass a ha I * bitClass (B:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hB.ne_zero) J =
    QuotientGroup.mk u
  rw [←hmk]
  change _ = classOf x hx
  exact (hcl.trans (congrArg (fun w => bitClass a ha I*w) hJ)).symm

theorem actualBasis_injective (hp2 : p≠2) (a : ℚ_[p]) (ha : a≠0) (haV : a.valuation=1)
    (B : ℤ_[p]) (hB : IsUnit B) (hBns : ¬IsSquare (PadicInt.toZMod B)) :
    Function.Injective (actualBasis a ha B hB) := by
  intro i j he
  let b : ℚ_[p] := B
  have hb : b≠0 := PadicInt.coe_ne_zero.mpr hB.ne_zero
  have hBv : b.valuation=0 := actual_val_zero_of_unit B hB
  have hI : i.1=j.1 := by
    have hRaw : classOf (bitValue a i.1*bitValue b i.2)
          (mul_ne_zero (bitValue_ne a ha _) (bitValue_ne b hb _)) =
        classOf (bitValue a j.1*bitValue b j.2)
          (mul_ne_zero (bitValue_ne a ha _) (bitValue_ne b hb _)) := by
      simpa only [actualBasis,bitClass,class_of_mul] using he
    obtain ⟨r,hr,hR⟩ := (class_of_eq_iff _ _ _ _).mp hRaw
    have hv := congrArg Padic.valuation hR
    rw [Padic.valuation_mul (bitValue_ne a ha _) (bitValue_ne b hb _),
      Padic.valuation_mul (mul_ne_zero (bitValue_ne a ha _) (bitValue_ne b hb _)) (pow_ne_zero 2 hr),
      Padic.valuation_mul (bitValue_ne a ha _) (bitValue_ne b hb _),
      Padic.valuation_pow] at hv
    simp only [bitValue_val,haV,hBv,ite_self,add_zero] at hv
    by_contra hn
    cases h₁ : i.1 <;> cases h₂ : j.1 <;> simp [h₁,h₂] at hv hn <;> omega
  have hE : bitClass a ha i.1*bitClass b hb i.2=bitClass a ha j.1*bitClass b hb j.2 := he
  rw [hI] at hE
  have hX : bitClass b hb i.2=bitClass b hb j.2 := mul_left_cancel hE
  have hU : classOf b hb≠1 := by
    intro hu
    rw [←class_of_one] at hu
    obtain ⟨r,hr,hR⟩ := (class_of_eq_iff _ _ _ _).mp hu
    exact hBns ((unit_square_iff_residue hp2 B hB).mp ⟨r,hr,by simpa only [one_mul,b] using hR⟩)
  have hJ : i.2=j.2 := by
    cases h₁ : i.2 <;> cases h₂ : j.2 <;>
      simp [h₁,h₂,bitClass_false,bitClass_true,hU,Ne.symm hU] at hX ⊢
  exact Prod.ext hI hJ

end CTOddSquareclassBasis318

#print axioms CTOddSquareclassBasis318.actualBasis_injective
#print axioms CTOddSquareclassBasis318.actualBasis_surjective
