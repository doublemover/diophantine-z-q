module
public import OriginalTensorComparisonSmallFrame318
public section
noncomputable section
namespace OriginalTensorComparisonRefinement318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι κ : Type u}
  (U : ι → Y.Opens) (V : κ → Y.Opens) (r : κ → ι) (hr : ∀k,V k≤U (r k))
  (M N : Y.Modules)
  (em : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (en : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ N.restrict (U i).ι)
  (hU : (⊤:Y.Opens)≤⨆i,U i) (hV : (⊤:Y.Opens)≤⨆k,V k)
/-- Refining the actual cover and frames reconstructs EXACTLY the same
tensor-pullback isomorphism. Every smaller index and full inverse image
is retained; no quotient by choice of cover is assumed. -/
lemma comparison :
    TensorPullbackCocycle318.comparison p U M N em en hU=
    TensorPullbackCocycle318.comparison p V M N
      (fun k => OpenLineFrameRefinement318.frame M (U (r k)) (em (r k)) (V k) (hr k))
      (fun k => OpenLineFrameRefinement318.frame N (U (r k)) (en (r k)) (V k) (hr k)) hV := by
  let fm := fun k => OpenLineFrameRefinement318.frame M (U (r k)) (em (r k)) (V k) (hr k)
  let fn := fun k => OpenLineFrameRefinement318.frame N (U (r k)) (en (r k)) (V k) (hr k)
  apply Iso.ext
  apply OriginalFramedComparisonNormalization318.hom_ext_restrict _ (fun k => p ⁻¹ᵁ V k)
    (TensorLineCocycle318.frames ((Scheme.Modules.pullback p).obj M)
      ((Scheme.Modules.pullback p).obj N) (fun k => p ⁻¹ᵁ V k)
      (fun k => LinePullbackFrames318.frame p M (V k) (fm k))
      (fun k => LinePullbackFrames318.frame p N (V k) (fn k)))
    (LinePullbackFrames318.preimage_cover p V hV)
  intro k
  apply (cancel_epi (LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor M N)
    (V k) (TensorLineLocalFrame318.frame M N (V k) (fm k) (fn k))).hom).mp
  exact (congrArg Iso.hom
    (OriginalTensorComparisonSmallFrame318.frame p U M N em en hU (r k) (V k) (hr k))).trans
      (congrArg Iso.hom
        (OriginalTensorPullbackFrameNormalization318.frame p V M N fm fn hV k)).symm
end OriginalTensorComparisonRefinement318
