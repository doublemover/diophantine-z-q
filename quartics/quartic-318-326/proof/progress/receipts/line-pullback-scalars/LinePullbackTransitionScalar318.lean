module
public import LinePullbackOriginalScalar318
public import OpenLineFrameRefinement318
public section
noncomputable section
namespace LinePullbackTransitionScalar318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) (U V W:Y.Opens)
    (hU:W≤U) (hV:W≤V)
    (eU:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (eV:SheafOfModules.unit V.toScheme.ringCatSheaf≅M.restrict V.ι)
/-- Reduction of the exact complete-overlap transition comparison to the
two actual canonical frame restriction identities. These identities are
explicit premises here and must be discharged by the coherence producer. -/
lemma of_restriction
    (h0:OpenLineFrameRefinement318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁU)
      (LinePullbackFrames318.frame f M U eU) (f⁻¹ᵁW) (f.preimage_mono hU)=
      LinePullbackFrames318.frame f M W (OpenLineFrameRefinement318.frame M U eU W hU))
    (h1:OpenLineFrameRefinement318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁV)
      (LinePullbackFrames318.frame f M V eV) (f⁻¹ᵁW) (f.preimage_mono hV)=
      LinePullbackFrames318.frame f M W (OpenLineFrameRefinement318.frame M V eV W hV)):
    FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁU)
        (LinePullbackFrames318.frame f M U eU) (f⁻¹ᵁW) (f.preimage_mono hU))
      (OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁV)
        (LinePullbackFrames318.frame f M V eV) (f⁻¹ᵁW) (f.preimage_mono hV))=
    Units.map (f.app W).hom.toMonoidHom (FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame M U eU W hU)
      (OpenLineFrameCoordinates318.frame M V eV W hV)):=by
  have h:=LinePullbackOriginalScalar318.scalar f M W
    (OpenLineFrameRefinement318.frame M U eU W hU)
    (OpenLineFrameRefinement318.frame M V eV W hV)
  rw [←h0,←h1] at h
  simpa only [OpenLineFrameRefinement318.coordinates] using h
end LinePullbackTransitionScalar318
