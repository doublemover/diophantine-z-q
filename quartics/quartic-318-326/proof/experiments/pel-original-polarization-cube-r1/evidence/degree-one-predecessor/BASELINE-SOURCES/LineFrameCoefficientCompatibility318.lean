module
public import ClutchedChartSections318
public import LineFrameCocycle318
public import CocycleModule318
public section
noncomputable section
namespace LineFrameCoefficientCompatibility318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 650000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
abbrev cocycle:=LineFrameCocycle318.cocycle M U frames
@[expose] def coefficient (i:ι):M⟶CocycleModule318.chart U i:=
  LineFrameAdjunction318.coordinate M (U i) (frames i)
lemma inverse_relation (i j:ι) (W:X.Opens) (h:W≤U i⊓U j) (s:Γ(M,W)):
    (OpenLineFrameCoordinates318.frame M (U i) (frames i) W (h.trans inf_le_left)).symm s=
      X.presheaf.map (homOfLE h).op ((cocycle M U frames).transition i j).val *
      (OpenLineFrameCoordinates318.frame M (U j) (frames j) W (h.trans inf_le_right)).symm s:=by
  apply (OpenLineFrameCoordinates318.frame M (U i) (frames i) W (h.trans inf_le_left)).injective
  rw [LinearEquiv.apply_symm_apply,LineFrameCocycle318.relation]
  exact (LinearEquiv.apply_symm_apply _ _).symm
/-- Actual original coefficient maps obey the cocycle module's exact
full-overlap sheaf-map equation, on every ambient open and every section. -/
lemma compatible (i j:ι):
    coefficient M U frames i≫CocycleModule318.left U i j=
      coefficient M U frames j≫CocycleModule318.right U (cocycle M U frames) i j:=by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply (ConcreteCategory.bijective_of_isIso
    (ClutchedChartSections318.overlapIso (U i) (U j) W).hom).injective
  change (ClutchedChartSections318.overlapIso (U i) (U j) W).hom
      ((ClutchedModule318.restriction (U i).ι
        (OpenClutchedLine318.leftInclusion (U i) (U j))).app W
          ((LineFrameAdjunction318.coordinate M (U i) (frames i)).app W s))=
    (ClutchedChartSections318.overlapIso (U i) (U j) W).hom
      ((ClutchedModule318.twistedRestriction (U i).ι (U j).ι
        (OpenClutchedLine318.leftInclusion (U i) (U j))
        (OpenClutchedLine318.rightInclusion (U i) (U j))
        (OpenClutchedLine318.square (U i) (U j))
        (OpenClutchedLine318.transition (U i) (U j) ((cocycle M U frames).transition i j))).app W
          ((LineFrameAdjunction318.coordinate M (U j) (frames j)).app W s))
  rw [ClutchedChartSections318.left_apply,ClutchedChartSections318.right_apply,
    LineFrameChartCoordinates318.coordinate_app,LineFrameChartCoordinates318.coordinate_app]
  rw [OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural]
  simp only [←M.presheaf.map_comp_apply,←op_comp,homOfLE_comp]
  rw [mul_comm]
  exact inverse_relation M U frames i j ((U i⊓U j)⊓W) inf_le_left
    (M.presheaf.map (homOfLE (show (U i⊓U j)⊓W≤W from inf_le_right)).op s)
end LineFrameCoefficientCompatibility318
