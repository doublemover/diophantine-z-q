module
public import CompletedAdditionRestrictions318
import all WeierstrassGluing318
public section
noncomputable section
namespace CompletedAdditionUnits318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 CompletedAdditionRestrictions318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def rightUnit (A B:R) : scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (𝟙 _) (structureMap A B ≫ infinity A B)
    (by simp only [Category.id_comp,Category.assoc,infinity_section,Category.comp_id])
@[expose] def leftUnit (A B:R) : scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (structureMap A B ≫ infinity A B) (𝟙 _)
    (by simp only [Category.id_comp,Category.assoc,infinity_section,Category.comp_id])
@[reassoc] theorem rightUnit_fst (A B:R) : rightUnit A B ≫ pullback.fst _ _=𝟙 _ := by simp [rightUnit]
@[reassoc] theorem rightUnit_snd (A B:R) : rightUnit A B ≫ pullback.snd _ _=structureMap A B ≫ infinity A B := by simp [rightUnit]
@[reassoc] theorem leftUnit_fst (A B:R) : leftUnit A B ≫ pullback.fst _ _=structureMap A B ≫ infinity A B := by simp [leftUnit]
@[reassoc] theorem leftUnit_snd (A B:R) : leftUnit A B ≫ pullback.snd _ _=𝟙 _ := by simp [leftUnit]

theorem finite_rightUnit (A B:R) : finiteChart A B ≫ rightUnit A B=
    SymmetricMixedAddition318.rightInfinity A B ≫ inputChart A B 0 1 := by
  apply pullback.hom_ext
  · rw [Category.assoc,rightUnit_fst,Category.comp_id,Category.assoc,inputChart_fst]
    change finiteChart A B=SymmetricMixedAddition318.rightInfinity A B ≫ pullback.fst _ _ ≫ finiteChart A B
    rw [←Category.assoc,SymmetricMixedAddition318.rightInfinity_fst,Category.id_comp]
  · rw [Category.assoc,rightUnit_snd,Category.assoc,inputChart_snd]
    change finiteChart A B ≫ structureMap A B ≫ infinity A B=
      SymmetricMixedAddition318.rightInfinity A B ≫ pullback.snd _ _ ≫ infinityChart A B
    rw [←Category.assoc,finiteChart_structure,←Category.assoc,SymmetricMixedAddition318.rightInfinity_snd,Category.assoc]
    rfl

@[expose] def finiteLeft (A B:R) : ShortAffineScheme318.scheme A B ⟶ InfinityInputScheme318.productScheme A B :=
  InfinityInputScheme318.infinityInput A B ≫ InfinityInputScheme318.intoProduct A B
@[reassoc] theorem finiteLeft_fst (A B:R) : finiteLeft A B ≫ pullback.fst _ _=
    ShortAffineScheme318.structureMap A B ≫ InfinitySmooth318.infinity A B := by
  simpa only [finiteLeft,Category.assoc] using InfinityInputScheme318.infinityInput_fst A B
@[reassoc] theorem finiteLeft_snd (A B:R) : finiteLeft A B ≫ pullback.snd _ _=𝟙 _ := by
  simpa only [finiteLeft,Category.assoc] using InfinityInputScheme318.infinityInput_snd A B

theorem finite_leftUnit (A B:R) : finiteChart A B ≫ leftUnit A B=
    finiteLeft A B ≫ inputChart A B 1 0 := by
  apply pullback.hom_ext
  · rw [Category.assoc,leftUnit_fst,Category.assoc,inputChart_fst]
    change finiteChart A B ≫ structureMap A B ≫ infinity A B=
      finiteLeft A B ≫ pullback.fst _ _ ≫ infinityChart A B
    rw [←Category.assoc,finiteChart_structure,finiteLeft_fst_assoc]
    rfl
  · rw [Category.assoc,leftUnit_snd,Category.comp_id,Category.assoc,inputChart_snd]
    change finiteChart A B=finiteLeft A B ≫ pullback.snd _ _ ≫ finiteChart A B
    rw [finiteLeft_snd_assoc]

end CompletedAdditionUnits318
