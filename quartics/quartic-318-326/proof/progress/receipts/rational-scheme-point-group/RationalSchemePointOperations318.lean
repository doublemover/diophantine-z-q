module
public import RationalGroupAssociativity318
public import CompletedLeftInverse318
public section
noncomputable section
namespace RationalSchemePointOperations318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Exact base-preserving points. The discriminant witness is retained in
the point type so the genuine group structure is unambiguous. -/
@[expose] def Points (A B:ℚ) (_hD:IsUnit (-16*(4*A^3+27*B^2))) {T:Scheme}
    (b:T ⟶ Spec (CommRingCat.of ℚ)):=
  {f:T ⟶ WeierstrassGluing318.scheme A B //f ≫ WeierstrassGluing318.structureMap A B=b}
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2))) {T:Scheme}
local notation "pE"=>WeierstrassGluing318.structureMap A B
variable (b:T ⟶ Spec (CommRingCat.of ℚ))
@[expose] def zero : Points A B hD b := ⟨b ≫ WeierstrassGluing318.infinity A B,by
  simp only [Category.assoc,WeierstrassGluing318.infinity_section,Category.comp_id]⟩
@[expose] def neg (p:Points A B hD b) : Points A B hD b := ⟨p.val ≫ GluedNegation318.negation A B,by
  rw [Category.assoc,GluedNegation318.negation_over_base];exact p.property⟩
@[expose] def pair (p q:Points A B hD b) : T ⟶ pullback pE pE :=
  pullback.lift p.val q.val (p.property.trans q.property.symm)
@[reassoc] theorem pair_fst (p q:Points A B hD b) : pair A B hD b p q ≫ pullback.fst _ _=p.val := by simp [pair]
@[reassoc] theorem pair_snd (p q:Points A B hD b) : pair A B hD b p q ≫ pullback.snd _ _=q.val := by simp [pair]
@[expose] def sum (p q:Points A B hD b) : Points A B hD b :=
  ⟨pair A B hD b p q ≫ CompletedAddition318.addition A B hD,by
    rw [Category.assoc,CompletedAddition318.addition_over_base,pair_fst_assoc]
    exact p.property⟩

theorem pair_zero_left (q:Points A B hD b) : pair A B hD b (zero A B hD b) q=
    q.val ≫ CompletedAdditionUnits318.leftUnit A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedAdditionUnits318.leftUnit_fst,←Category.assoc,q.property]
    rfl
  · rw [pair_snd,Category.assoc,CompletedAdditionUnits318.leftUnit_snd,Category.comp_id]
theorem pair_zero_right (p:Points A B hD b) : pair A B hD b p (zero A B hD b)=
    p.val ≫ CompletedAdditionUnits318.rightUnit A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedAdditionUnits318.rightUnit_fst,Category.comp_id]
  · rw [pair_snd,Category.assoc,CompletedAdditionUnits318.rightUnit_snd,←Category.assoc,p.property]
    rfl
theorem zero_sum (q:Points A B hD b) : sum A B hD b (zero A B hD b) q=q := by
  apply Subtype.ext
  change pair A B hD b (zero A B hD b) q ≫ CompletedAddition318.addition A B hD=q.val
  rw [pair_zero_left,Category.assoc,CompletedAdditionUnits318.leftUnit_addition,Category.comp_id]
theorem sum_zero (p:Points A B hD b) : sum A B hD b p (zero A B hD b)=p := by
  apply Subtype.ext
  change pair A B hD b p (zero A B hD b) ≫ CompletedAddition318.addition A B hD=p.val
  rw [pair_zero_right,Category.assoc,CompletedAdditionUnits318.rightUnit_addition,Category.comp_id]

theorem pair_neg_left (p:Points A B hD b) : pair A B hD b (neg A B hD b p) p=
    p.val ≫ CompletedLeftInverse318.antiDiagonal A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedLeftInverse318.antiDiagonal_fst]
    rfl
  · rw [pair_snd,Category.assoc,CompletedLeftInverse318.antiDiagonal_snd,Category.comp_id]
theorem pair_neg_right (p:Points A B hD b) : pair A B hD b p (neg A B hD b p)=
    p.val ≫ CompletedAdditionInverse318.antiDiagonal A B := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedAdditionInverse318.antiDiagonal_fst,Category.comp_id]
  · rw [pair_snd,Category.assoc,CompletedAdditionInverse318.antiDiagonal_snd]
    rfl
theorem neg_sum (p:Points A B hD b) : sum A B hD b (neg A B hD b p) p=zero A B hD b := by
  apply Subtype.ext
  change pair A B hD b (neg A B hD b p) p ≫ CompletedAddition318.addition A B hD=b ≫ WeierstrassGluing318.infinity A B
  rw [pair_neg_left,Category.assoc,CompletedLeftInverse318.antiDiagonal_addition,←Category.assoc,p.property]
theorem sum_neg (p:Points A B hD b) : sum A B hD b p (neg A B hD b p)=zero A B hD b := by
  apply Subtype.ext
  change pair A B hD b p (neg A B hD b p) ≫ CompletedAddition318.addition A B hD=b ≫ WeierstrassGluing318.infinity A B
  rw [pair_neg_right,Category.assoc,CompletedAdditionInverse318.antiDiagonal_addition,←Category.assoc,p.property]

theorem pair_swap (p q:Points A B hD b) : pair A B hD b p q ≫ (pullbackSymmetry pE pE).hom=pair A B hD b q p := by
  apply pullback.hom_ext
  · simp only [Category.assoc,pullbackSymmetry_hom_comp_fst,pair_snd,pair_fst]
  · simp only [Category.assoc,pullbackSymmetry_hom_comp_snd,pair_fst,pair_snd]
theorem sum_comm (p q:Points A B hD b) : sum A B hD b p q=sum A B hD b q p := by
  apply Subtype.ext
  change pair A B hD b p q ≫ CompletedAddition318.addition A B hD=pair A B hD b q p ≫ CompletedAddition318.addition A B hD
  rw [←pair_swap,Category.assoc,CompletedAdditionCommutative318.addition_commutative]
end RationalSchemePointOperations318
