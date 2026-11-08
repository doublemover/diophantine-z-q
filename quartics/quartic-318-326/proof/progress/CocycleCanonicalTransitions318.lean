module
public import LineFrameCocycleReconstruction318
public import CocycleActualLocalFrame318
public section
noncomputable section
namespace CocycleCanonicalTransitions318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
abbrev M:=CocycleModule318.object U c
/-- The original coefficient-transpose frames, without changing the sheaf. -/
@[expose] def frames (i:ι):SheafOfModules.unit (U i).toScheme.ringCatSheaf≅
    (M U c).restrict (U i).ι:=(CocycleActualLocalFrame318.frame U c i).symm
lemma coordinate (i:ι):LineFrameAdjunction318.coordinate (M U c) (U i) (frames U c i)=
    CocycleModule318.coefficient U c i:=by
  apply ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv
    (M U c) (SheafOfModules.unit (U i).toScheme.ringCatSheaf)).symm.injective
  rw [LineFrameAdjunction318.transpose]
  rfl
lemma compatible (i j:ι):
    LineFrameAdjunction318.coordinate (M U c) (U i) (frames U c i)≫CocycleModule318.left U i j=
      LineFrameAdjunction318.coordinate (M U c) (U j) (frames U c j)≫CocycleModule318.right U c i j:=by
  rw [coordinate,coordinate]
  exact CocycleModule318.compatible U c i j
/-- The supplied transition is recovered on the complete original overlap. -/
lemma inverse_relation (i j:ι) (s:Γ(M U c,U i⊓U j)):
    (OpenLineFrameCoordinates318.frame (M U c) (U i) (frames U c i)
      (U i⊓U j) inf_le_left).symm s=
    (OpenLineFrameCoordinates318.frame (M U c) (U j) (frames U c j)
      (U i⊓U j) inf_le_right).symm s * (c.transition i j).val:=by
  let W:=U i⊓U j
  have h:=congrArg (fun f=>(ClutchedChartSections318.overlapIso (U i) (U j) W).hom
    (f.app W s)) (compatible U c i j)
  change (ClutchedChartSections318.overlapIso (U i) (U j) W).hom
    ((ClutchedModule318.restriction (U i).ι
      (OpenClutchedLine318.leftInclusion (U i) (U j))).app W
        ((LineFrameAdjunction318.coordinate (M U c) (U i) (frames U c i)).app W s))=
    (ClutchedChartSections318.overlapIso (U i) (U j) W).hom
      ((ClutchedModule318.twistedRestriction (U i).ι (U j).ι
        (OpenClutchedLine318.leftInclusion (U i) (U j))
        (OpenClutchedLine318.rightInclusion (U i) (U j))
        (OpenClutchedLine318.square (U i) (U j))
        (OpenClutchedLine318.transition (U i) (U j) (c.transition i j))).app W
          ((LineFrameAdjunction318.coordinate (M U c) (U j) (frames U c j)).app W s)) at h
  rw [ClutchedChartSections318.left_apply,ClutchedChartSections318.right_apply,
    LineFrameChartCoordinates318.coordinate_app,LineFrameChartCoordinates318.coordinate_app] at h
  rw [OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural] at h
  simp only [←(M U c).presheaf.map_comp_apply,←op_comp,homOfLE_comp] at h
  have he:(U i⊓U j)⊓W=W:=by dsimp [W];exact le_antisymm inf_le_left (le_inf le_rfl le_rfl)
  let e:=X.presheaf.mapIso (eqToIso he).op
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  change X.presheaf.map (homOfLE he.le).op _=X.presheaf.map (homOfLE he.le).op _
  rw [map_mul,OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural]
  exact h
lemma cocycle_eq:LineFrameCocycle318.cocycle (M U c) U (frames U c)=c:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame (M U c) (U i) (frames U c i)
    (U i⊓U j) inf_le_left).symm
      (OpenLineFrameCoordinates318.frame (M U c) (U j) (frames U c j)
        (U i⊓U j) inf_le_right 1)=(c.transition i j).val
  rw [inverse_relation,LinearEquiv.symm_apply_apply,one_mul]
end CocycleCanonicalTransitions318
