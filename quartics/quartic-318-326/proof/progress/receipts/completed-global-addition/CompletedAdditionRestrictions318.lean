module
public import CompletedAddition318
public section
noncomputable section
namespace CompletedAdditionRestrictions318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318 CompletedAdditionCharts318 CompletedAdditionCompatibility318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def inputChart (A B:R) (i j:Fin 2) :
    pullback (chartStructure A B i) (chartStructure A B j) ⟶
      pullback (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B) :=
  (chartProductIso A B i j).inv ≫ (productCover A B).f ⟨i,j⟩
@[reassoc] theorem inputChart_fst (A B:R) (i j:Fin 2) :
    inputChart A B i j ≫ pullback.fst _ _=pullback.fst _ _ ≫ intoCurve A B i := by
  rw [inputChart,Category.assoc,←first_input,Iso.inv_hom_id_assoc]
@[reassoc] theorem inputChart_snd (A B:R) (i j:Fin 2) :
    inputChart A B i j ≫ pullback.snd _ _=pullback.snd _ _ ≫ intoCurve A B j := by
  rw [inputChart,Category.assoc,←second_input,Iso.inv_hom_id_assoc]
@[reassoc] theorem inputChart_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    inputChart A B i j ≫ CompletedAddition318.addition A B hD=chartAddition A B hD i j := by
  rw [inputChart,Category.assoc,CompletedAddition318.restriction,localAddition,Iso.inv_hom_id_assoc]
end CompletedAdditionRestrictions318
