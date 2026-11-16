module
public import OriginalTensorComparisonCoverIndependence318
public section
noncomputable section
namespace OriginalTensorPullbackAllCoverNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι κ : Type u}
  (U : ι → Y.Opens) (V : κ → Y.Opens)
  {M N M' N' : Y.Modules} (a : M ≅ M') (b : N ≅ N')
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (fm : ∀ k,SheafOfModules.unit (V k).toScheme.ringCatSheaf ≅ M'.restrict (V k).ι)
  (fn : ∀ k,SheafOfModules.unit (V k).toScheme.ringCatSheaf ≅ N'.restrict (V k).ι)
  (hU : (⊤:Y.Opens)≤⨆i,U i) (hV : (⊤:Y.Opens)≤⨆k,V k)
/-- The literal original tensor-pullback square for independently
specified source and target presentations. The cover compatibility is
now proved, not supplied as a naturality hypothesis. -/
lemma natural :
    (Scheme.Modules.pullback p).mapIso (TensorSheafFunctor318.congr a b) ≪≫
      TensorPullbackCocycle318.comparison p V M' N' fm fn hV=
    TensorPullbackCocycle318.comparison p U M N em en hU ≪≫
      TensorSheafFunctor318.congr ((Scheme.Modules.pullback p).mapIso a)
        ((Scheme.Modules.pullback p).mapIso b) := by
  rw [←OriginalTensorComparisonCoverIndependence318.comparison p U V M' N'
    (fun i => em i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso a)
    (fun i => en i ≪≫ (Scheme.Modules.restrictFunctor (U i).ι).mapIso b) fm fn hU hV]
  exact OriginalTensorPullbackNaturality318.natural p U a b em en hU
end OriginalTensorPullbackAllCoverNaturality318
