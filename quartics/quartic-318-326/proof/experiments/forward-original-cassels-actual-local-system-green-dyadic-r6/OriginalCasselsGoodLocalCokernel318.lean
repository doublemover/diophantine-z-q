module
public import OriginalCasselsOddLocalFinite318
public import OriginalCasselsGoodLift318
public import OriginalCasselsOddUnitCharacter318
import all OriginalCasselsDyadicXClass318
import all OriginalCasselsOddLocalFinite318
import all OriginalCasselsLiteralIsogenyPoint318
import all OriginalSelectedCasselsParity318
public section

noncomputable section

namespace OriginalCasselsGoodLocalCokernel318

open OriginalCasselsGoodLift318 OriginalCasselsOddUnitCharacter318
open OriginalCasselsOddTargetValuation318 OriginalCasselsOddUnitSquare318
open OriginalCasselsRamifiedResidue318 ActualTwoDescentLocalValuationTools318
open OriginalCasselsOddLocalFinite318 OriginalCasselsLiteralRangeFinite318
open OriginalCasselsDyadicXClass318 OriginalCasselsTargetClassChord318
open OriginalCasselsLiteralIsogenyAddition318 OriginalCasselsLiteralIsogenyPoint318
open OriginalSelectedCasselsParity318 ActualTwoDescentSquareClassQuotient318

variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

private theorem target_equation (n x y : ℚ_[p]) (H : (targetModel n).toAffine.Nonsingular x y) :
    y^2=x*(x^2-4*n*x+16*n^2) := by
  have h := H.left
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [targetModel,zero_mul,add_zero,zero_add] at h
  linear_combination h

private theorem val_four (hp : 5≤p) : (4:ℚ_[p]).valuation=0 := by
  have h : ¬p∣4 := fun hd => (by omega : ¬p≤4) (Nat.le_of_dvd (by decide : 0<4) hd)
  simpa only [Nat.cast_ofNat] using actual_prime_unit_valuation (p:=p) 4 h

/-- Exactly a trivial class and one actual nonsquare-unit class at the
literal good prime. No global arithmetic or finite-field group law. -/
theorem good_actual_two_classes (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N) :
    ∃ P₀ : TargetPoint (N:ℚ_[p]), targetClass P₀≠1 ∧
      ∀ P : TargetPoint (N:ℚ_[p]), targetClass P=1 ∨ targetClass P=targetClass P₀ := by
  let n : ℚ_[p] := N
  have hn : n≠0 := PadicInt.coe_ne_zero.mpr hN.ne_zero
  have hp2 : p≠2 := by omega
  have hv : ((4:ℚ_[p])*n).valuation=0 := by
    rw [Padic.valuation_mul (by norm_num : (4:ℚ_[p])≠0) hn,val_four hp,
      actual_val_zero_of_unit N hN,add_zero]
  obtain ⟨X,Y,hX,hXS,hE⟩ := exists_lifted_nonsquare_abscissa hp N hN
  have hx : (X:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hX.ne_zero
  have hE' : (Y:ℚ_[p])^2=(X:ℚ_[p])*((X:ℚ_[p])^2-4*n*(X:ℚ_[p])+16*n^2) := by
    dsimp [n]
    exact_mod_cast hE
  let P₀ := targetPoint n (X:ℚ_[p]) (Y:ℚ_[p]) hn hE'
  have hc₀ : targetClass P₀=classOf (X:ℚ_[p]) hx := target_class_at_affine hn hx hE'
  refine ⟨P₀,?_,?_⟩
  · intro h
    rw [hc₀,←class_of_one] at h
    obtain ⟨s,hs,e⟩ := (class_of_eq_iff _ _ hx one_ne_zero).mp h
    exact hXS ((unit_square_iff_residue hp2 X hX).1 ⟨s,hs,by simpa only [one_mul] using e⟩)
  · intro P
    cases P with
    | zero => exact Or.inl rfl
    | some x y H =>
      by_cases hx' : x=0
      · subst x
        exact Or.inl (by simp [targetClass])
      · have he := target_equation n x y H
        change targetClass (targetPoint n x y hn he)=1 ∨ targetClass (targetPoint n x y hn he)=targetClass P₀
        rw [target_class_at_affine hn hx' he,hc₀,←class_of_one]
        by_cases hxv : x.valuation=0
        · let A : ℤ_[p] := ⟨x,(actual_norm_one_of_valuation_zero x hx' hxv).le⟩
          have hA : IsUnit A := PadicInt.isUnit_iff.mpr (actual_norm_one_of_valuation_zero x hx' hxv)
          by_cases hS : IsSquare (PadicInt.toZMod A)
          · left
            obtain ⟨s,hs,hE⟩ := (unit_square_iff_residue hp2 A hA).2 hS
            exact (class_of_eq_iff _ _ hx' one_ne_zero).2 ⟨s,hs,by simpa only [one_mul] using hE⟩
          · right
            obtain ⟨s,hs,hE⟩ := unit_ratio_square_of_nonsquare hp2 A X hA hX hS hXS
            exact (class_of_eq_iff _ _ hx' hx).2 ⟨s,hs,hE⟩
        · left
          obtain ⟨s,hs,hE⟩ := abscissa_square_of_factor_square n x y hx' he
            (factor_square_of_unequal_val hp2 n x hn hx' (fun h => hxv (h.trans hv)))
          exact (class_of_eq_iff _ _ hx' one_ne_zero).2 ⟨s,hs,by simpa only [one_mul] using hE⟩

/-- At p≥5 of good reduction, the constructed actual local isogeny has
cokernel of size two. Its range is the exact quotient by the literal
hom, with no independently supplied count or point map. -/
theorem actual_good_cokernel_card (hp : 5≤p) (hp2 : p≠2) (N : ℤ_[p]) (hN : IsUnit N) :
    (localOddIsogeny hp2 (N:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hN.ne_zero)).cokernelCard=2 := by
  let n : ℚ_[p] := N
  have hn : n≠0 := PadicInt.coe_ne_zero.mpr hN.ne_zero
  let H := xClassHom (actual_target_class_product n hn)
  let img (P : TargetPoint n) : H.range := ⟨H P,⟨P,rfl⟩⟩
  obtain ⟨P₀,hne,hclasses⟩ := good_actual_two_classes hp N hN
  let f : Bool → H.range := fun b => if b then img P₀ else img 0
  have hf : f true≠f false := by
    intro h
    apply hne
    exact congrArg Subtype.val h
  have hi : Function.Injective f := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact (hf h.symm).elim
    · exact (hf h).elim
    · rfl
  have hs : Function.Surjective f := by
    rintro ⟨z,P,rfl⟩
    rcases hclasses P with h|h
    · exact ⟨false,Subtype.ext h.symm⟩
    · exact ⟨true,Subtype.ext h.symm⟩
  change Nat.card (TargetPoint n ⧸ (literalHom (literal_addition n hn)).range)=2
  rw [Nat.card_congr (literalQuotientEquiv n hn).toEquiv,
    Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩).symm, Nat.card_eq_fintype_card] <;> decide

end OriginalCasselsGoodLocalCokernel318

#print axioms OriginalCasselsGoodLocalCokernel318.good_actual_two_classes
#print axioms OriginalCasselsGoodLocalCokernel318.actual_good_cokernel_card
