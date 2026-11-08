module
public import RationalCompletedAdditionPoints318
public import CompletedAdditionTriple318
public section
noncomputable section
namespace RationalAssociativityTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RationalCompletedAdditionPoints318 CompletedAdditionTriple318
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {K:Type} [Field K] [Algebra ℚ K]
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
include hD
@[expose] def point1
    (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple A B)
    (hb:t ≫ CompletedAdditionTriple318.first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) :
    RationalCompletedAdditionPoints318.Points (K:=K) A B hD :=
  ⟨t ≫ CompletedAdditionTriple318.first A B, (Category.assoc _ _ _).trans hb⟩
@[expose] def point2
    (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple A B)
    (hb:t ≫ CompletedAdditionTriple318.first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) :
    RationalCompletedAdditionPoints318.Points (K:=K) A B hD :=
  ⟨t ≫ CompletedAdditionTriple318.second A B, (Category.assoc _ _ _).trans ((congrArg (fun f=>t ≫ f) (CompletedAdditionTriple318.first_second_base A B).symm).trans hb)⟩
@[expose] def point3
    (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple A B)
    (hb:t ≫ CompletedAdditionTriple318.first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) :
    RationalCompletedAdditionPoints318.Points (K:=K) A B hD :=
  ⟨t ≫ CompletedAdditionTriple318.third A B, (Category.assoc _ _ _).trans ((congrArg (fun f=>t ≫ f) (CompletedAdditionTriple318.first_third_base A B).symm).trans hb)⟩
theorem pair12_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : pointPair A B hD (point1 A B hD t hb) (point2 A B hD t hb)=t ≫ pair12 A B := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,pair12_fst]
    rfl
  · rw [pointPair_snd,Category.assoc,pair12_snd]
    rfl
theorem pair23_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : pointPair A B hD (point2 A B hD t hb) (point3 A B hD t hb)=t ≫ pair23 A B := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,pair23_fst]
    rfl
  · rw [pointPair_snd,Category.assoc,pair23_snd]
    rfl
theorem sum12_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : (sumPoint A B hD (point1 A B hD t hb) (point2 A B hD t hb)).val=
    t ≫ pair12 A B ≫ CompletedAddition318.addition A B hD := by
  change pointPair A B hD (point1 A B hD t hb) (point2 A B hD t hb) ≫ _=_
  rw [pair12_point,Category.assoc]
theorem sum23_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : (sumPoint A B hD (point2 A B hD t hb) (point3 A B hD t hb)).val=
    t ≫ pair23 A B ≫ CompletedAddition318.addition A B hD := by
  change pointPair A B hD (point2 A B hD t hb) (point3 A B hD t hb) ≫ _=_
  rw [pair23_point,Category.assoc]
theorem leftPair_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : pointPair A B hD (sumPoint A B hD (point1 A B hD t hb) (point2 A B hD t hb)) (point3 A B hD t hb)=
    t ≫ leftPair A B hD := by
  apply pullback.hom_ext
  · rw [pointPair_fst,sum12_value,Category.assoc,leftPair_fst]
  · rw [pointPair_snd,Category.assoc,leftPair_snd]
    rfl
theorem rightPair_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : pointPair A B hD (point1 A B hD t hb) (sumPoint A B hD (point2 A B hD t hb) (point3 A B hD t hb))=
    t ≫ rightPair A B hD := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,rightPair_fst]
    rfl
  · rw [pointPair_snd,sum23_value,Category.assoc,rightPair_snd]
theorem left_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : (sumPoint A B hD (sumPoint A B hD (point1 A B hD t hb) (point2 A B hD t hb)) (point3 A B hD t hb)).val=
    t ≫ leftAssociate A B hD := by
  change pointPair A B hD (sumPoint A B hD (point1 A B hD t hb) (point2 A B hD t hb)) (point3 A B hD t hb) ≫ _=_
  rw [leftPair_point,Category.assoc,leftAssociate]
theorem right_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : (sumPoint A B hD (point1 A B hD t hb) (sumPoint A B hD (point2 A B hD t hb) (point3 A B hD t hb))).val=
    t ≫ rightAssociate A B hD := by
  change pointPair A B hD (point1 A B hD t hb) (sumPoint A B hD (point2 A B hD t hb) (point3 A B hD t hb)) ≫ _=_
  rw [rightPair_point,Category.assoc,rightAssociate]
/-- Both actual associativity composites agree after every field-valued test
morphism over the original literal base. -/
theorem field_test
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap ℚ K) : t ≫ leftAssociate A B hD=t ≫ rightAssociate A B hD := by
  have hh:=congrArg Subtype.val (sumPoint_assoc A B hD (point1 A B hD t hb) (point2 A B hD t hb) (point3 A B hD t hb))
  rw [left_value,right_value] at hh
  exact hh
end RationalAssociativityTest318
