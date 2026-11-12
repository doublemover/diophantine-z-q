module
public import OriginalFramedComparisonNormalization318
public import TensorPullbackCocycle318
public section
noncomputable section
namespace OriginalTensorPullbackFrameNormalization318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
  (M N : Y.Modules)
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤:Y.Opens)≤⨆i,U i)
/-- The ACTUAL reconstructed tensor-pullback comparison sends each
original pulled tensor frame to the tensor of the original pulled frames
on the ENTIRE inverse-image chart. No substitute monoidal map is assumed. -/
lemma frame (i : ι) :
    LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor M N) (U i)
      (TensorLineCocycle318.frames M N U em en i) ≪≫
        (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U i).ι).mapIso
          (TensorPullbackCocycle318.comparison p U M N em en hc)=
    TensorLineCocycle318.frames ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback p).obj N) (fun i => p ⁻¹ᵁ U i)
      (fun i => LinePullbackFrames318.frame p M (U i) (em i))
      (fun i => LinePullbackFrames318.frame p N (U i) (en i)) i :=
  OriginalFramedComparisonNormalization318.frame _ _ _ _ _ _ _ i
end OriginalTensorPullbackFrameNormalization318
