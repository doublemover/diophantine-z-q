module
public import FramedTensorCommutor318
public import StructureLineFrames318
public section
noncomputable section
namespace FramedTensorUnit318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
abbrev unitObject (X:Scheme.{u}):X.Modules:=SheafOfModules.unit X.ringCatSheaf
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
@[expose] def unitFrames (i:ι):SheafOfModules.unit (U i).toScheme.ringCatSheaf≅(unitObject X).restrict (U i).ι:=
  StructureLineFrames318.frame X (U i)
lemma unit_cocycle:
    LineFrameCocycle318.cocycle (unitObject X) U (unitFrames U)=
      UnitCocycleOne318.one (StructureUnitsSheaf318.units X).obj U:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact StructureLineFrames318.transition_one X U i j
lemma cocycle_eq:
    LineFrameCocycle318.cocycle (tensor (unitObject X) M) U
      (TensorLineCocycle318.frames (unitObject X) M U (unitFrames U) em)=
      LineFrameCocycle318.cocycle M U em:=
  (TensorLineCocycle318.cocycle_eq (unitObject X) M U (unitFrames U) em).trans
    ((congrArg (fun c=>UnitCocycleProduct318.product c (LineFrameCocycle318.cocycle M U em))
      (unit_cocycle U)).trans (UnitCocycleProductLaws318.one_product _))
variable (hc:(⊤:X.Opens)≤⨆i,U i)
@[expose] def leftIso:tensor (unitObject X) M≅M:=
  FramedLineCocycleIso318.iso _ _ U
    (TensorLineCocycle318.frames (unitObject X) M U (unitFrames U) em) em hc (cocycle_eq M U em)
@[expose] def rightIso:tensor M (unitObject X)≅M:=
  FramedTensorCommutor318.iso M (unitObject X) U em (unitFrames U) hc ≪≫leftIso M U em hc
lemma left_hom_inv:(leftIso M U em hc).hom≫(leftIso M U em hc).inv=𝟙 _:=
  (leftIso M U em hc).hom_inv_id
lemma left_inv_hom:(leftIso M U em hc).inv≫(leftIso M U em hc).hom=𝟙 _:=
  (leftIso M U em hc).inv_hom_id
lemma right_hom_inv:(rightIso M U em hc).hom≫(rightIso M U em hc).inv=𝟙 _:=
  (rightIso M U em hc).hom_inv_id
lemma right_inv_hom:(rightIso M U em hc).inv≫(rightIso M U em hc).hom=𝟙 _:=
  (rightIso M U em hc).inv_hom_id
end FramedTensorUnit318
