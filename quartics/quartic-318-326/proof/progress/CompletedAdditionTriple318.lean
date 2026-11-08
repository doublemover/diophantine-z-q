module
public import CompletedAddition318
public section
noncomputable section
namespace CompletedAdditionTriple318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def product (A B:R) := pullback (structureMap A B) (structureMap A B)
@[expose] def productBase (A B:R) : product A B ⟶ Spec (CommRingCat.of R) :=
  pullback.fst _ _ ≫ structureMap A B
@[expose] def triple (A B:R) := pullback (productBase A B) (structureMap A B)
@[expose] def first (A B:R) : triple A B ⟶ scheme A B := pullback.fst _ _ ≫ pullback.fst _ _
@[expose] def second (A B:R) : triple A B ⟶ scheme A B := pullback.fst _ _ ≫ pullback.snd _ _
@[expose] def third (A B:R) : triple A B ⟶ scheme A B := pullback.snd _ _
@[expose] def pair12 (A B:R) : triple A B ⟶ product A B := pullback.fst _ _
@[reassoc] theorem pair12_fst (A B:R) : pair12 A B ≫ pullback.fst _ _=first A B := rfl
@[reassoc] theorem pair12_snd (A B:R) : pair12 A B ≫ pullback.snd _ _=second A B := rfl
lemma first_second_base (A B:R) : first A B ≫ structureMap A B=second A B ≫ structureMap A B := by
  simp only [first,second,Category.assoc,pullback.condition]
lemma first_third_base (A B:R) : first A B ≫ structureMap A B=third A B ≫ structureMap A B := by
  change (pullback.fst (productBase A B) (structureMap A B) ≫ pullback.fst _ _) ≫ structureMap A B=_
  rw [Category.assoc]
  exact pullback.condition
@[expose] def pair23 (A B:R) : triple A B ⟶ product A B :=
  pullback.lift (second A B) (third A B) ((first_second_base A B).symm.trans (first_third_base A B))
@[reassoc] theorem pair23_fst (A B:R) : pair23 A B ≫ pullback.fst _ _=second A B := by simp [pair23]
@[reassoc] theorem pair23_snd (A B:R) : pair23 A B ≫ pullback.snd _ _=third A B := by simp [pair23]

variable (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
@[expose] def leftPair : triple A B ⟶ product A B :=
  pullback.lift (pair12 A B ≫ CompletedAddition318.addition A B hD) (third A B) (by
    rw [Category.assoc,CompletedAddition318.addition_over_base,pair12_fst_assoc]
    exact first_third_base A B)
@[expose] def rightPair : triple A B ⟶ product A B :=
  pullback.lift (first A B) (pair23 A B ≫ CompletedAddition318.addition A B hD) (by
    rw [Category.assoc,CompletedAddition318.addition_over_base,pair23_fst_assoc]
    exact first_second_base A B)
@[reassoc] theorem leftPair_fst : leftPair A B hD ≫ pullback.fst _ _=pair12 A B ≫ CompletedAddition318.addition A B hD := by simp [leftPair]
@[reassoc] theorem leftPair_snd : leftPair A B hD ≫ pullback.snd _ _=third A B := by simp [leftPair]
@[reassoc] theorem rightPair_fst : rightPair A B hD ≫ pullback.fst _ _=first A B := by simp [rightPair]
@[reassoc] theorem rightPair_snd : rightPair A B hD ≫ pullback.snd _ _=pair23 A B ≫ CompletedAddition318.addition A B hD := by simp [rightPair]
@[expose] def leftAssociate : triple A B ⟶ scheme A B := leftPair A B hD ≫ CompletedAddition318.addition A B hD
@[expose] def rightAssociate : triple A B ⟶ scheme A B := rightPair A B hD ≫ CompletedAddition318.addition A B hD
lemma leftAssociate_base : leftAssociate A B hD ≫ structureMap A B=first A B ≫ structureMap A B := by
  rw [leftAssociate,Category.assoc,CompletedAddition318.addition_over_base,leftPair_fst_assoc,
    CompletedAddition318.addition_over_base,pair12_fst_assoc]
lemma rightAssociate_base : rightAssociate A B hD ≫ structureMap A B=first A B ≫ structureMap A B := by
  rw [rightAssociate,Category.assoc,CompletedAddition318.addition_over_base,rightPair_fst_assoc]
end CompletedAdditionTriple318
