module
public import LineFrameIsoTransport318
public import InverseImageLineCocycle318
public section
noncomputable section
namespace LineFrameIsoCocycle318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X:Scheme.{u}} {M N:X.Modules} (e:M≅N) {ι:Type v} (V:ι→X.Opens)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
@[expose] def transported (i:ι):SheafOfModules.unit (V i).toScheme.ringCatSheaf≅N.restrict (V i).ι:=
  LineFrameIsoTransport318.transported e (V i) (frames i)
lemma scalar (i j:ι) (W:X.Opens) (hi:W≤V i) (hj:W≤V j):
    LineFrameTransitions318.scalar N V (transported e V frames) i j W hi hj=
      LineFrameTransitions318.scalar M V frames i j W hi hj:=by
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame N (V i) (transported e V frames i) W hi).symm
    (OpenLineFrameCoordinates318.frame N (V j) (transported e V frames j) W hj 1)=
    (OpenLineFrameCoordinates318.frame M (V i) (frames i) W hi).symm
      (OpenLineFrameCoordinates318.frame M (V j) (frames j) W hj 1)
  simp only [transported]
  rw [LineFrameIsoTransport318.coordinates,LineFrameIsoTransport318.inverse_coordinates]
lemma cocycle_eq:
    LineFrameCocycle318.cocycle N V (transported e V frames)=
      LineFrameCocycle318.cocycle M V frames:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact scalar e V frames i j (V i⊓V j) inf_le_left inf_le_right
variable {Y:Scheme.{u}} (f:X⟶Y) (U:ι→Y.Opens)
    (sourceFrames:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
/-- Equality of the exact pushed-unit cocycles on whole inverse-image
intersections after transporting by the original source-line isomorphism. -/
lemma inverseImage_eq:
    InverseImageLineCocycle318.cocycle f N U
      (transported e (fun i=>f⁻¹ᵁU i) sourceFrames)=
    InverseImageLineCocycle318.cocycle f M U sourceFrames:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact scalar e (fun i=>f⁻¹ᵁU i) sourceFrames i j (f⁻¹ᵁ(U i⊓U j))
    (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
end LineFrameIsoCocycle318
