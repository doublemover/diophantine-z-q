module
public import ChartSchemeCompatibility318
public section
noncomputable section
namespace CompletedAdditionCompatibility318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318 CompletedAdditionCharts318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[reassoc] theorem first_input (A B:R) (i j:Fin 2) :
    (chartProductIso A B i j).hom ≫ pullback.fst _ _ ≫ intoCurve A B i=
      (productCover A B).f ⟨i,j⟩ ≫ pullback.fst _ _ := by
  rw [chartProductIso_fst_assoc]
  exact (GenericProductCover318.fst (cover A B) (cover A B)
    (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B) i j).symm
@[reassoc] theorem second_input (A B:R) (i j:Fin 2) :
    (chartProductIso A B i j).hom ≫ pullback.snd _ _ ≫ intoCurve A B j=
      (productCover A B).f ⟨i,j⟩ ≫ pullback.snd _ _ := by
  rw [chartProductIso_snd_assoc]
  exact (GenericProductCover318.snd (cover A B) (cover A B)
    (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B) i j).symm

theorem local_compatibility (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j k l:Fin 2) :
    pullback.fst ((productCover A B).f ⟨i,j⟩) ((productCover A B).f ⟨k,l⟩) ≫ localAddition A B hD i j=
      pullback.snd _ _ ≫ localAddition A B hD k l := by
  rw [localAddition,localAddition,←Category.assoc,←Category.assoc]
  apply ChartSchemeCompatibility318.scheme_agreement
  · simp only [Category.assoc,first_input]
    simpa only [Category.assoc] using congrArg (fun f=>f ≫ pullback.fst (WeierstrassGluing318.structureMap A B)
      (WeierstrassGluing318.structureMap A B)) pullback.condition
  · simp only [Category.assoc,second_input]
    simpa only [Category.assoc] using congrArg (fun f=>f ≫ pullback.snd (WeierstrassGluing318.structureMap A B)
      (WeierstrassGluing318.structureMap A B)) pullback.condition
end CompletedAdditionCompatibility318
