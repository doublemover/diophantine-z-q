module
public import ClutchedChartSections318
public import LineFrameAdjunction318
public section
noncomputable section
namespace OriginalClutchedFrameTransition318
open AlgebraicGeometry CategoryTheory Opposite
open OpenClutchedLine318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (U V : X.Opens) (a : Γ(X,U ⊓ V)ˣ)
abbrev M := line U V a

/-- The existing first full-open frame has exactly the original clutched
first projection as its restriction-adjunction transpose. -/
lemma first_coordinate :
    LineFrameAdjunction318.coordinate (M U V a) U (firstFrame U V a).symm =
      ClutchedModule318.first U.ι V.ι (leftInclusion U V) (rightInclusion U V)
        (square U V) (transition U V a) := by
  apply ((Scheme.Modules.restrictAdjunction U.ι).homEquiv
    (M U V a) (SheafOfModules.unit U.toScheme.ringCatSheaf)).symm.injective
  rw [LineFrameAdjunction318.transpose]
  rfl

lemma second_coordinate :
    LineFrameAdjunction318.coordinate (M U V a) V (secondFrame U V a).symm =
      ClutchedModule318.second U.ι V.ι (leftInclusion U V) (rightInclusion U V)
        (square U V) (transition U V a) := by
  apply ((Scheme.Modules.restrictAdjunction V.ι).homEquiv
    (M U V a) (SheafOfModules.unit V.toScheme.ringCatSheaf)).symm.injective
  rw [LineFrameAdjunction318.transpose]
  rfl

/-- The actual existing chart frames recover the specified original
regular transition on EVERY section of the WHOLE original intersection. -/
lemma inverse_relation (s : Γ(M U V a,U ⊓ V)) :
    (OpenLineFrameCoordinates318.frame (M U V a) U (firstFrame U V a).symm
      (U ⊓ V) inf_le_left).symm s =
    (OpenLineFrameCoordinates318.frame (M U V a) V (secondFrame U V a).symm
      (U ⊓ V) inf_le_right).symm s * a.val := by
  let W := U ⊓ V
  have hc := ClutchedModule318.compatibility U.ι V.ι
    (leftInclusion U V) (rightInclusion U V) (square U V) (transition U V a)
  rw [← first_coordinate U V a,← second_coordinate U V a] at hc
  have h := congrArg (fun f => (ClutchedChartSections318.overlapIso U V W).hom
    (f.app W s)) hc
  change (ClutchedChartSections318.overlapIso U V W).hom
    ((ClutchedModule318.restriction U.ι (leftInclusion U V)).app W
      ((LineFrameAdjunction318.coordinate (M U V a) U (firstFrame U V a).symm).app W s)) =
    (ClutchedChartSections318.overlapIso U V W).hom
      ((ClutchedModule318.twistedRestriction U.ι V.ι (leftInclusion U V)
        (rightInclusion U V) (square U V) (transition U V a)).app W
          ((LineFrameAdjunction318.coordinate (M U V a) V (secondFrame U V a).symm).app W s)) at h
  rw [ClutchedChartSections318.left_apply,ClutchedChartSections318.right_apply,
    LineFrameChartCoordinates318.coordinate_app,LineFrameChartCoordinates318.coordinate_app] at h
  rw [OpenLineFrameCoordinates318.inverse_natural,OpenLineFrameCoordinates318.inverse_natural] at h
  simp only [← (M U V a).presheaf.map_comp_apply,← op_comp,homOfLE_comp] at h
  have he : (U ⊓ V) ⊓ W = W := by
    dsimp [W]
    exact le_antisymm inf_le_left (le_inf le_rfl le_rfl)
  let e := X.presheaf.mapIso (eqToIso he).op
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  change X.presheaf.map (homOfLE he.le).op _ = X.presheaf.map (homOfLE he.le).op _
  rw [map_mul,OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural]
  exact h
end OriginalClutchedFrameTransition318
