module
public import LineFrameTransitions318
public import UnitTransitionCocycle318
public import StructureUnitsSheaf318
public section
noncomputable section
namespace LineFrameCocycle318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type v} (V:ι→X.Opens)
  (frames:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
/-- Actual transition units of the original line frames on every complete
overlap. Left coordinates equal transition times right coordinates. -/
@[expose] def cocycle:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj V where
  transition i j:=LineFrameTransitions318.scalar M V frames i j (V i⊓V j) inf_le_left inf_le_right
  diagonal i:=LineFrameTransitions318.self M V frames i (V i⊓V i) inf_le_left
  triple i j k:=by
    change Units.map (X.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom _ *
      Units.map (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op).hom.toMonoidHom _ =
      Units.map (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op).hom.toMonoidHom _
    rw [LineFrameTransitions318.restrict,LineFrameTransitions318.restrict,LineFrameTransitions318.restrict]
    exact LineFrameTransitions318.comp M V frames i j k _ _ _ _
/-- The actual section equation on every subopen of the full overlap,
not merely a pointwise or global-coefficient test. -/
lemma relation (i j:ι) (W:X.Opens) (h:W≤V i⊓V j) (s:Γ(X,W)):
    OpenLineFrameCoordinates318.frame M (V i) (frames i) W (h.trans inf_le_left)
      ((X.presheaf.map (homOfLE h).op ((cocycle M V frames).transition i j).val)*s)=
    OpenLineFrameCoordinates318.frame M (V j) (frames j) W (h.trans inf_le_right) s:=by
  have hr:=congrArg Units.val (LineFrameTransitions318.restrict M V frames i j inf_le_left inf_le_right h)
  change OpenLineFrameCoordinates318.frame M (V i) (frames i) W (h.trans inf_le_left)
    ((X.presheaf.map (homOfLE h).op ((cocycle M V frames).transition i j).val)*s)=_
  rw [show X.presheaf.map (homOfLE h).op ((cocycle M V frames).transition i j).val=
    (LineFrameTransitions318.scalar M V frames i j W (h.trans inf_le_left) (h.trans inf_le_right)).val from hr]
  exact LineFrameTransitions318.relation M V frames i j W _ _ s
end LineFrameCocycle318
