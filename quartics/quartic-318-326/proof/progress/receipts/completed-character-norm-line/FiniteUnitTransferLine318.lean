module
public import FiniteUnitTransferPresentation318
public import CocycleCanonicalTransitions318
public section
noncomputable section
namespace FiniteUnitTransferLine318
open AlgebraicGeometry CategoryTheory
open FiniteUnitTransferPresentation318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsFinite f] (M:X.Modules)
    {ι:Type u} (A:ι→X.Opens) (hA:(⊤:X.Opens)≤⨆i,A i)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
/-- A genuine target module sheaf from the actual transferred original units. -/
@[expose] def object:Y.Modules:=CocycleModule318.object (targetOpen f M A hA eA)
  (targetCocycle f M A hA eA unitMap)
@[expose] def frame (y:Y):
    SheafOfModules.unit (targetOpen f M A hA eA y).toScheme.ringCatSheaf≅
      (object f M A hA eA unitMap).restrict (targetOpen f M A hA eA y).ι:=
  CocycleCanonicalTransitions318.frames (targetOpen f M A hA eA)
    (targetCocycle f M A hA eA unitMap) y
lemma frame_hom_inv (y:Y):(frame f M A hA eA unitMap y).hom≫
    (frame f M A hA eA unitMap y).inv=𝟙 _ :=(frame f M A hA eA unitMap y).hom_inv_id
lemma frame_inv_hom (y:Y):(frame f M A hA eA unitMap y).inv≫
    (frame f M A hA eA unitMap y).hom=𝟙 _ :=(frame f M A hA eA unitMap y).inv_hom_id
lemma locallyFree:(object f M A hA eA unitMap).IsLocallyFree:=
  CocycleActualLocalFrame318.locallyFree _ _ (target_cover f M A hA eA)
/-- The actual target's original coefficient frames recover exactly the
transferred cocycle on every complete original overlap. -/
lemma original_transitions:
    LineFrameCocycle318.cocycle (object f M A hA eA unitMap) (targetOpen f M A hA eA)
      (frame f M A hA eA unitMap)=targetCocycle f M A hA eA unitMap:=
  CocycleCanonicalTransitions318.cocycle_eq _ _
lemma coefficients (y z:Y):
    CocycleModule318.coefficient (targetOpen f M A hA eA) (targetCocycle f M A hA eA unitMap) y≫
      CocycleModule318.left (targetOpen f M A hA eA) y z=
    CocycleModule318.coefficient (targetOpen f M A hA eA) (targetCocycle f M A hA eA unitMap) z≫
      CocycleModule318.right (targetOpen f M A hA eA) (targetCocycle f M A hA eA unitMap) y z:=
  CocycleModule318.compatible _ _ y z
end FiniteUnitTransferLine318
