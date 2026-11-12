module
public import OriginalTensorComparisonRefinement318
public section
noncomputable section
namespace OriginalTensorComparisonCoverIndependence318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι κ : Type u}
  (U : ι → Y.Opens) (V : κ → Y.Opens) (M N : Y.Modules)
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (fm : ∀ k,SheafOfModules.unit (V k).toScheme.ringCatSheaf ≅ M.restrict (V k).ι)
  (fn : ∀ k,SheafOfModules.unit (V k).toScheme.ringCatSheaf ≅ N.restrict (V k).ι)
  (hU : (⊤:Y.Opens)≤⨆i,U i) (hV : (⊤:Y.Opens)≤⨆k,V k)
/-- Arbitrary independent covers and frames yield the SAME original
map. Compare through the actual product-index intersection cover; retain
all indices and cancel frame choices only after exact refinement. -/
lemma comparison :
    TensorPullbackCocycle318.comparison p U M N em en hU=
      TensorPullbackCocycle318.comparison p V M N fm fn hV := by
  let W := fun q : ι × κ => U q.1 ⊓ V q.2
  have hW : (⊤:Y.Opens)≤⨆q,W q := UnitCocycleRefinement318.common_cover U V hU hV
  have hleft := OriginalTensorComparisonRefinement318.comparison p U W Prod.fst
    (fun _ => inf_le_left) M N em en hU hW
  have hright := OriginalTensorComparisonRefinement318.comparison p V W Prod.snd
    (fun _ => inf_le_right) M N fm fn hV hW
  exact hleft.trans ((OriginalTensorPullbackFrameIndependence318.comparison p W M N
    _ _ _ _ hW).trans hright.symm)
end OriginalTensorComparisonCoverIndependence318
