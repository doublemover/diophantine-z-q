module
public import OriginalFrameCoordinateExt318
public section
noncomputable section
namespace OriginalFrameRefinementNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)
  (U W : X.Opens) (h : W≤U)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
/-- Refinement transports the SAME full module isomorphism, with both
native restriction maps retained, on the entire smaller open. -/
lemma frame :
    OpenLineFrameRefinement318.frame N U
      (e ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso a) W h=
    OpenLineFrameRefinement318.frame M U e W h ≪≫
      (Scheme.Modules.restrictFunctor W.ι).mapIso a := by
  apply OriginalFrameCoordinateExt318.coordinates N W
  intro Z hZ
  apply LinearEquiv.ext
  intro s
  rw [OpenLineFrameRefinement318.coordinates,LineFrameIsoTransport318.coordinates,
    LineFrameIsoTransport318.coordinates,OpenLineFrameRefinement318.coordinates]
end OriginalFrameRefinementNaturality318
