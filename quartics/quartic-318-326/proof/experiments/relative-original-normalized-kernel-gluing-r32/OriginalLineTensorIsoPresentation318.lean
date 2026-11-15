module
public import OriginalTensorComparisonCoefficientComposition318
public section
noncomputable section
namespace OriginalLineTensorIsoPresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (L N : Line Y) {ι : Type u}
  (U : ι → Y.Opens)
  (em : ∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ L.object.restrict (U i).ι)
  (en : ∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.object.restrict (U i).ι)
  (hc : (⊤:Y.Opens)≤⨆i,U i)
/-- Every genuine common presentation computes the SAME old tensorIso.
This includes the pulled original cover, not only a newly chosen common
refinement of the pullback Line records. -/
lemma comparison : TensorPullbackCocycle318.comparison p U L.object N.object em en hc=
    LineClassPullbackHom318.tensorIso p L N :=
  OriginalTensorComparisonCoverIndependence318.comparison p U
    (fun q : L.Index × N.Index => L.opens q.1 ⊓ N.opens q.2) L.object N.object em en
    (fun q => OpenLineFrameRefinement318.frame L.object (L.opens q.1) (L.frame q.1)
      (L.opens q.1 ⊓ N.opens q.2) inf_le_left)
    (fun q => OpenLineFrameRefinement318.frame N.object (N.opens q.2) (N.frame q.2)
      (L.opens q.1 ⊓ N.opens q.2) inf_le_right) hc
    (UnitCocycleRefinement318.common_cover L.opens N.opens L.cover N.cover)
end OriginalLineTensorIsoPresentation318
