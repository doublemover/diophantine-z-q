module
public import OriginalCasselsOddUnitSquare318
public import OriginalCasselsLiteralRangeFinite318
public import Lean.Elab.Tactic.Omega
import all ActualTwoDescentSquareClassQuotient318
public section

noncomputable section

namespace OriginalCasselsOddLocalFinite318

open OriginalCasselsOddUnitSquare318 ActualTwoDescentSquareClassQuotient318
open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralIsogenyAddition318
open OriginalCasselsLiteralRangeFinite318 OriginalCasselsDyadicXClass318
open OriginalCasselsTargetClassChord318 OriginalSelectedCasselsParity318

variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

private theorem residue_val_ne_zero (r : ZMod p) (hr : r≠0) : r.val≠0 := by
  intro h
  apply hr
  rw [← ZMod.natCast_zmod_val r,h,Nat.cast_zero]

private def representative (i : Fin 2) (r : ZMod p) : ℚ_[p] :=
  (p:ℚ_[p])^(i.val:ℤ)*(if r=0 then 1 else (r.val:ℚ_[p]))

private theorem representative_ne_zero (i : Fin 2) (r : ZMod p) :
    representative i r≠0 := by
  unfold representative
  apply mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  split_ifs with h
  · exact one_ne_zero
  · exact Nat.cast_ne_zero.mpr (residue_val_ne_zero r h)

/-- Every actual class has a finite residue representative. This proves
finiteness only; it does not assert that every representative appears on
the original quotient curve or that all these labels are different. -/
theorem actual_squareclass_finite (hp2 : p≠2) : Finite (SquareClass ℚ_[p]) := by
  let f : Fin 2 × ZMod p → SquareClass ℚ_[p] := fun z =>
    classOf (representative z.1 z.2) (representative_ne_zero z.1 z.2)
  apply Finite.of_surjective f
  intro q
  refine QuotientGroup.induction_on q ?_
  intro u
  let x : ℚ_[p] := (u:ℚ_[p])
  have hx : x≠0 := u.ne_zero
  obtain ⟨U,hU,he⟩ := actual_odd_unit_normal x hx
  let r := PadicInt.toZMod U
  have hr : r≠0 := (hU.map PadicInt.toZMod).ne_zero
  let B : ℤ_[p] := r.val
  have hB : PadicInt.toZMod B=r := by simp only [B,map_natCast,ZMod.natCast_zmod_val]
  have hev : (B:ℚ_[p])=(r.val:ℚ_[p]) := by
    change (((r.val:ℤ_[p]):ℚ_[p]))=(r.val:ℚ_[p])
    norm_cast
  obtain ⟨z,hz,hzU⟩ := unit_ratio_square_of_equal_residue hp2 U B
    (fun h => hr (hB.symm.trans h)) hB.symm
  let i : Fin 2 := ⟨(x.valuation%2).toNat,by omega⟩
  have hi : x.valuation=(i.val:ℤ)+(x.valuation/2)*2 := by
    dsimp [i]
    omega
  have hp0 : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine ⟨(i,r),?_⟩
  have hMk : Units.mk0 x hx = u := by ext; rfl
  change classOf (representative i r) (representative_ne_zero i r)=QuotientGroup.mk u
  rw [←hMk]
  change classOf (representative i r) (representative_ne_zero i r)=classOf x hx
  symm
  apply (class_of_eq_iff x _ hx _).mpr
  refine ⟨(p:ℚ_[p])^(x.valuation/2)*z,mul_ne_zero (zpow_ne_zero _ hp0) hz,?_⟩
  calc
    x = (p:ℚ_[p])^x.valuation*(U:ℚ_[p]) := he
    _ = _ := by
      rw [hzU,hev]
      unfold representative
      rw [if_neg hr]
      conv_lhs => rw [hi,zpow_add₀ hp0,zpow_mul]
      rw [zpow_natCast]
      ring

/-- No hypothesis about a chosen local isogeny or a local count.
All local maps act on the literal original and quotient point groups. -/
theorem literal_odd_quotient_finite (hp2 : p≠2) (n : ℚ_[p]) (hn : n≠0) :
    Finite (TargetPoint n ⧸ (literalHom (literal_addition n hn)).range) := by
  letI := actual_squareclass_finite hp2
  have hF : Finite (xClassHom (actual_target_class_product n hn)).range :=
    Finite.of_injective (fun z => Additive.toMul z.val) (by
      intro a b h
      exact Subtype.ext h)
  letI := hF
  exact Finite.of_equiv _ (literalQuotientEquiv n hn).symm.toEquiv

def localOddIsogeny (hp2 : p≠2) (n : ℚ_[p]) (hn : n≠0) : LocalIsogeny n hn :=
  localIsogeny (literal_addition n hn) (literal_odd_quotient_finite hp2 n hn)

end OriginalCasselsOddLocalFinite318

#print axioms OriginalCasselsOddLocalFinite318.literal_odd_quotient_finite
