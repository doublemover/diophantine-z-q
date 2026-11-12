module
public import OriginalTensorFrameRefinement318
public import LinePullbackFrameCoherence318
public section
noncomputable section
namespace OriginalTensorComparisonSmallFrame318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
  (M N : Y.Modules)
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hc : (⊤:Y.Opens)≤⨆i,U i)
/-- The SAME global comparison is normalized on every whole smaller
original chart. This uses the pre-existing native pullback-frame
coherence, not an assumed common-refinement compatibility. -/
lemma frame (i : ι) (W : Y.Opens) (hW : W≤U i) :
    LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor M N) W
      (TensorLineLocalFrame318.frame M N W
        (OpenLineFrameRefinement318.frame M (U i) (em i) W hW)
        (OpenLineFrameRefinement318.frame N (U i) (en i) W hW)) ≪≫
      (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ W).ι).mapIso
        (TensorPullbackCocycle318.comparison p U M N em en hc)=
    TensorLineLocalFrame318.frame ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback p).obj N) (p ⁻¹ᵁ W)
      (LinePullbackFrames318.frame p M W (OpenLineFrameRefinement318.frame M (U i) (em i) W hW))
      (LinePullbackFrames318.frame p N W (OpenLineFrameRefinement318.frame N (U i) (en i) W hW)) := by
  have h0 := OriginalTensorPullbackFrameNormalization318.frame p U M N em en hc i
  have hh := congrArg (fun e => OpenLineFrameRefinement318.frame
    (IntrinsicTensorSheaf318.tensor ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback p).obj N)) (p ⁻¹ᵁ U i) e (p ⁻¹ᵁ W) (p.preimage_mono hW)) h0
  dsimp only [TensorLineCocycle318.frames] at hh
  rw [OriginalFrameRefinementNaturality318.frame,LinePullbackFrameCoherence318.frame,
    OriginalTensorFrameRefinement318.frame,OriginalTensorFrameRefinement318.frame,
    LinePullbackFrameCoherence318.frame,LinePullbackFrameCoherence318.frame] at hh
  exact hh
end OriginalTensorComparisonSmallFrame318
