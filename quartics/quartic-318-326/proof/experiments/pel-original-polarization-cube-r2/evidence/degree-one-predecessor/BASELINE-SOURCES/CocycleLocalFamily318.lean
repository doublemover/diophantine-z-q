module
public import CocycleTwistedCoordinates318
public import UnitSourceExt318
public section
noncomputable section
namespace CocycleLocalFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CocycleLocalCoefficients318 CocycleOverlapCoordinates318 CocycleTwistedCoordinates318
set_option maxHeartbeats 450000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
lemma compatible (i j k:ι):
    localMap U c i j≫localLeft U i j k=localMap U c i k≫localRight U c i j k:=by
  apply UnitSourceExt318.ext (localOverlap U i j k)
  change (localLeft U i j k).app ⊤ ((localMap U c i j).app ⊤ (1:Γ((U i).toScheme,⊤)))=
    (localRight U c i j k).app ⊤ ((localMap U c i k).app ⊤ (1:Γ((U i).toScheme,⊤)))
  rw [localMap_one,localMap_one]
  apply (ConcreteCategory.bijective_of_isIso (overlapIso U i j k).hom).injective
  change (overlapIso U i j k).hom ((localLeft U i j k).app ⊤ ((coefficientIso U i j).inv (c.transition j i).val))=
    (overlapIso U i j k).hom ((localRight U c i j k).app ⊤ ((coefficientIso U i k).inv (c.transition k i).val))
  rw [left_coordinate,right_coordinate]
  have h:=congrArg Units.val (UnitCocycleSubopens318.transition_mul c j k i
    (show (U j⊓U k)⊓U i≤U j from inf_le_left.trans inf_le_left)
    (show (U j⊓U k)⊓U i≤U k from inf_le_left.trans inf_le_right)
    (show (U j⊓U k)⊓U i≤U i from inf_le_right))
  exact h.symm.trans (mul_comm _ _)
lemma localSection_diagonal (i:ι):localSection U c i i=
    (1:Γ((U i).toScheme,(U i).ι⁻¹ᵁ((U i).ι ''ᵁ ⊤))):=by
  change (coefficientIso U i i).inv (c.transition i i).val=1
  rw [c.diagonal]
  exact map_one (coefficientIso U i i).inv.hom
@[expose] def counit (i:ι):localChart U i i⟶ClutchedModule318.unit (U i).toScheme:=
  (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (ClutchedModule318.unit (U i).toScheme)
instance counit_iso (i:ι):IsIso (counit U i):=by unfold counit;infer_instance
lemma diagonal_counit (i:ι):localMap U c i i≫counit U i=𝟙 _:=by
  apply UnitSourceExt318.ext (ClutchedModule318.unit (U i).toScheme)
  change (counit U i).app ⊤ ((localMap U c i i).app ⊤ (1:Γ((U i).toScheme,⊤)))=(1:Γ((U i).toScheme,⊤))
  rw [localMap_one,localSection_diagonal]
  change (U i).toScheme.presheaf.map _ (1:Γ((U i).toScheme,_))=1
  exact map_one _
instance diagonal_iso (i:ι):IsIso (localMap U c i i):=by
  haveI:IsIso (localMap U c i i≫counit U i):=by rw [diagonal_counit];infer_instance
  exact IsIso.of_isIso_comp_right _ (counit U i)
end CocycleLocalFamily318
