module
public import OpenLineFrameRefinement318
public import InverseImageLineCocycle318
public section
noncomputable section
namespace StructureLineFrames318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable (X:Scheme.{u})
@[expose] def frame (U:X.Opens):
    SheafOfModules.unit U.toScheme.ringCatSheaf≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules).restrict U.ι:=
  OpenLineFrameRefinement318.fromOver (SheafOfModules.unit X.ringCatSheaf) U (Iso.refl _)
lemma coordinates (U W:X.Opens) (h:W≤U):
    OpenLineFrameCoordinates318.frame (SheafOfModules.unit X.ringCatSheaf)
      U (frame X U) W h=LinearEquiv.refl Γ(X,W) Γ(X,W):=by
  unfold OpenLineFrameCoordinates318.frame frame
  rw [OpenLineFrameRefinement318.over_fromOver]
  rfl
lemma transition_one {ι:Type v} (U:ι→X.Opens) (i j:ι):
    (LineFrameCocycle318.cocycle (SheafOfModules.unit X.ringCatSheaf) U
      (fun k=>frame X (U k))).transition i j=1:=by
  change FrameScalarAlgebra318.scalar _ _=1
  rw [coordinates,coordinates]
  exact FrameScalarAlgebra318.self _
lemma inverseImage_transition_one {Y:Scheme.{u}} (f:X⟶Y) {ι:Type v}
    (U:ι→Y.Opens) (i j:ι):
    (InverseImageLineCocycle318.cocycle f (SheafOfModules.unit X.ringCatSheaf) U
      (fun k=>frame X (f⁻¹ᵁU k))).transition i j=1:=by
  change FrameScalarAlgebra318.scalar _ _=1
  rw [coordinates,coordinates]
  exact FrameScalarAlgebra318.self _
end StructureLineFrames318
