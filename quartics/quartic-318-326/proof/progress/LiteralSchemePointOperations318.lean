module
public import LiteralGroupAssociativity318
public import CompletedLeftInverse318
public section
noncomputable section
namespace LiteralSchemePointOperations318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "pE" => WeierstrassGluing318.structureMap A B
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
/-- Actual base-preserving maps from any test Scheme, not only field points. -/
@[expose] def Points := {f:T ⟶ WeierstrassGluing318.scheme A B // f ≫ pE=b}
@[expose] def zero : Points N b := ⟨b ≫ WeierstrassGluing318.infinity A B,by
  simp only [Category.assoc,WeierstrassGluing318.infinity_section,Category.comp_id]⟩
@[expose] def neg (p:Points N b) : Points N b := ⟨p.val ≫ GluedNegation318.negation A B,by
  rw [Category.assoc,GluedNegation318.negation_over_base];exact p.property⟩
@[expose] def pair (p q:Points N b) : T ⟶ pullback pE pE :=
  pullback.lift p.val q.val (p.property.trans q.property.symm)
@[reassoc] theorem pair_fst (p q:Points N b) : pair N b p q ≫ pullback.fst _ _=p.val := by simp [pair]
@[reassoc] theorem pair_snd (p q:Points N b) : pair N b p q ≫ pullback.snd _ _=q.val := by simp [pair]
@[expose] def sum (p q:Points N b) : Points N b :=
  ⟨pair N b p q ≫ CompletedAddition318.addition A B hD,by
    rw [Category.assoc,CompletedAddition318.addition_over_base,pair_fst_assoc]
    exact p.property⟩

theorem pair_zero_left (q:Points N b) : pair N b (zero N b) q=
    q.val ≫ CompletedAdditionUnits318.leftUnit A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedAdditionUnits318.leftUnit_fst,←Category.assoc,q.property]
    rfl
  · rw [pair_snd,Category.assoc,CompletedAdditionUnits318.leftUnit_snd,Category.comp_id]
theorem pair_zero_right (p:Points N b) : pair N b p (zero N b)=
    p.val ≫ CompletedAdditionUnits318.rightUnit A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedAdditionUnits318.rightUnit_fst,Category.comp_id]
  · rw [pair_snd,Category.assoc,CompletedAdditionUnits318.rightUnit_snd,←Category.assoc,p.property]
    rfl
theorem zero_sum (q:Points N b) : sum N b (zero N b) q=q := by
  apply Subtype.ext
  change pair N b (zero N b) q ≫ CompletedAddition318.addition A B hD=q.val
  rw [pair_zero_left,Category.assoc,CompletedAdditionUnits318.leftUnit_addition,Category.comp_id]
theorem sum_zero (p:Points N b) : sum N b p (zero N b)=p := by
  apply Subtype.ext
  change pair N b p (zero N b) ≫ CompletedAddition318.addition A B hD=p.val
  rw [pair_zero_right,Category.assoc,CompletedAdditionUnits318.rightUnit_addition,Category.comp_id]

theorem pair_neg_left (p:Points N b) : pair N b (neg N b p) p=
    p.val ≫ CompletedLeftInverse318.antiDiagonal A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedLeftInverse318.antiDiagonal_fst]
    rfl
  · rw [pair_snd,Category.assoc,CompletedLeftInverse318.antiDiagonal_snd,Category.comp_id]
theorem pair_neg_right (p:Points N b) : pair N b p (neg N b p)=
    p.val ≫ CompletedAdditionInverse318.antiDiagonal A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedAdditionInverse318.antiDiagonal_fst,Category.comp_id]
  · rw [pair_snd,Category.assoc,CompletedAdditionInverse318.antiDiagonal_snd]
    rfl
theorem neg_sum (p:Points N b) : sum N b (neg N b p) p=zero N b := by
  apply Subtype.ext
  change pair N b (neg N b p) p ≫ CompletedAddition318.addition A B hD=b ≫ WeierstrassGluing318.infinity A B
  rw [pair_neg_left,Category.assoc,CompletedLeftInverse318.antiDiagonal_addition,←Category.assoc,p.property]
theorem sum_neg (p:Points N b) : sum N b p (neg N b p)=zero N b := by
  apply Subtype.ext
  change pair N b p (neg N b p) ≫ CompletedAddition318.addition A B hD=b ≫ WeierstrassGluing318.infinity A B
  rw [pair_neg_right,Category.assoc,CompletedAdditionInverse318.antiDiagonal_addition,←Category.assoc,p.property]

theorem pair_swap (p q:Points N b) : pair N b p q ≫ (pullbackSymmetry pE pE).hom=pair N b q p := by
  apply pullback.hom_ext
  · simp only [Category.assoc,pullbackSymmetry_hom_comp_fst,pair_snd,pair_fst]
  · simp only [Category.assoc,pullbackSymmetry_hom_comp_snd,pair_fst,pair_snd]
theorem sum_comm (p q:Points N b) : sum N b p q=sum N b q p := by
  apply Subtype.ext
  change pair N b p q ≫ CompletedAddition318.addition A B hD=pair N b q p ≫ CompletedAddition318.addition A B hD
  rw [←pair_swap,Category.assoc,CompletedAdditionCommutative318.addition_commutative]
end LiteralSchemePointOperations318
