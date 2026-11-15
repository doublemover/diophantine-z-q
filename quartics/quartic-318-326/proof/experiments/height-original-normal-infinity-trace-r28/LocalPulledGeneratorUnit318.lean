module
public import LocalPullbackFrameGenerator318
public import PullbackFrameCoefficient318
public section
noncomputable section
namespace LocalPulledGeneratorUnit318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)(M:Y.Modules)(U:Y.Opens)
  (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
  (s:Γ(M,U))
  (hs:IsUnit ((OpenLineFrameCoordinates318.frame M U e U le_rfl).symm s))
/-- Actual chart-unit normalization makes the original local generator
a genuine generator in the canonical pulled frame on the whole inverse
image. This is derived, not an extra source-generation premise. -/
theorem whole:
    IsUnit ((OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M)
      (f⁻¹ᵁU) (LinePullbackFrames318.frame f M U e) (f⁻¹ᵁU) le_rfl).symm
        (LocalPullbackUnit318.pull f M U s)):=
  PullbackFrameCoefficient318.generator_unit f M U
    (OpenLineFrameCoordinates318.frame M U e U le_rfl)
    (OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M)
      (f⁻¹ᵁU) (LinePullbackFrames318.frame f M U e) (f⁻¹ᵁU) le_rfl)
    (LocalPullbackFrameGenerator318.generator f M U e) s hs
/-- The same regular unit persists on EVERY genuine source subopen,
through the actual coefficient restriction map of the canonical frame. -/
theorem subopen(V:X.Opens)(h:V≤f⁻¹ᵁU):
    IsUnit ((OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback f).obj M)
      (f⁻¹ᵁU) (LinePullbackFrames318.frame f M U e) V h).symm
        (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op
          (LocalPullbackUnit318.pull f M U s))):=by
  rw [←OpenLineFrameCoordinates318.inverse_natural
    ((Scheme.Modules.pullback f).obj M) (f⁻¹ᵁU) (LinePullbackFrames318.frame f M U e)
      le_rfl h]
  exact (whole f M U e s hs).map (X.presheaf.map (homOfLE h).op).hom
end LocalPulledGeneratorUnit318
