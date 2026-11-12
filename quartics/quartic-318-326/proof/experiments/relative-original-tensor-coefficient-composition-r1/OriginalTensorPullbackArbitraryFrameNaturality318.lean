module
public import OriginalTensorPullbackFrameIndependence318
public section
noncomputable section
namespace OriginalTensorPullbackArbitraryFrameNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
  {M N M' N' : Y.Modules} (a : M ≅ M') (b : N ≅ N')
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (em' : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M'.restrict (U i).ι)
  (en' : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N'.restrict (U i).ι)
  (hc : (⊤:Y.Opens)≤⨆i,U i)
/-- Full two-slot naturality on the original cover with ARBITRARY
independently supplied target frames. The transported-frame restriction
is removed by the constructed unit-ratio gauge cancellation, not assumed. -/
lemma natural :
    (Scheme.Modules.pullback p).mapIso (TensorSheafFunctor318.congr a b) ≪≫
      TensorPullbackCocycle318.comparison p U M' N' em' en' hc=
    TensorPullbackCocycle318.comparison p U M N em en hc ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullback p).mapIso a)
        ((Scheme.Modules.pullback p).mapIso b) := by
  rw [←OriginalTensorPullbackFrameIndependence318.comparison p U M' N'
    (fun i => em i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso a) em'
    (fun i => en i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso b) en' hc]
  exact OriginalTensorPullbackNaturality318.natural p U a b em en hc
end OriginalTensorPullbackArbitraryFrameNaturality318
