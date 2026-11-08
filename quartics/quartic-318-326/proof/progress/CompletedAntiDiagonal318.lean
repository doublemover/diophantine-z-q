module
public import CompletedAdditionRestrictions318
public import FiniteInverseScheme318
public import GluedNegation318
public section
noncomputable section
namespace CompletedAdditionInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 CompletedAdditionRestrictions318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def antiDiagonal (A B:R) : scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (𝟙 _) (GluedNegation318.negation A B)
    (by simp only [Category.id_comp,GluedNegation318.negation_over_base])
@[reassoc] theorem antiDiagonal_fst (A B:R) : antiDiagonal A B ≫ pullback.fst _ _=𝟙 _ := by
  simp [antiDiagonal]
@[reassoc] theorem antiDiagonal_snd (A B:R) : antiDiagonal A B ≫ pullback.snd _ _=GluedNegation318.negation A B := by
  simp [antiDiagonal]

theorem finite_antiDiagonal (A B:R) : finiteChart A B ≫ antiDiagonal A B=
    FiniteInverseScheme318.antiDiagonal A B ≫ inputChart A B 0 0 := by
  apply pullback.hom_ext
  · rw [Category.assoc,antiDiagonal_fst,Category.comp_id,Category.assoc,inputChart_fst]
    change finiteChart A B=FiniteInverseScheme318.antiDiagonal A B ≫ pullback.fst _ _ ≫ finiteChart A B
    rw [←Category.assoc,FiniteInverseScheme318.antiDiagonal_fst,Category.id_comp]
  · rw [Category.assoc,antiDiagonal_snd,GluedNegation318.finiteChart_negation,Category.assoc,inputChart_snd]
    change GluedNegation318.finiteNeg A B ≫ finiteChart A B=
      FiniteInverseScheme318.antiDiagonal A B ≫ pullback.snd _ _ ≫ finiteChart A B
    rw [←Category.assoc,FiniteInverseScheme318.antiDiagonal_snd]
    rfl

end CompletedAdditionInverse318
