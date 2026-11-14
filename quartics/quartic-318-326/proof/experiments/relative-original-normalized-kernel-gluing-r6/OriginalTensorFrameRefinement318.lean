module
public import OriginalFrameRefinementNaturality318
public section
noncomputable section
namespace OriginalTensorFrameRefinement318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U W : X.Opens) (h : W≤U)
  (em : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (en : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι)
/-- The ACTUAL tensor chart frame restricts to the tensor of the ACTUAL
restricted frames, including the native tensor/open comparison. Inverse
maps are tested on all pure sections on all smaller chart opens. -/
lemma frame :
    OpenLineFrameRefinement318.frame (IntrinsicTensorSheaf318.tensor M N) U
      (TensorLineLocalFrame318.frame M N U em en) W h=
    TensorLineLocalFrame318.frame M N W
      (OpenLineFrameRefinement318.frame M U em W h)
      (OpenLineFrameRefinement318.frame N U en W h) := by
  let e := OpenLineFrameRefinement318.frame (IntrinsicTensorSheaf318.tensor M N) U
    (TensorLineLocalFrame318.frame M N U em en) W h
  let d := TensorLineLocalFrame318.frame M N W
    (OpenLineFrameRefinement318.frame M U em W h)
    (OpenLineFrameRefinement318.frame N U en W h)
  have hi : e.symm=d.symm := by
    apply Iso.ext
    apply (cancel_epi (TensorOpenRestriction318.iso W.ι M N).inv).mp
    apply OriginalTensorFrameChange318.pure_ext (M.restrict W.ι) (N.restrict W.ι)
    intro Z m n
    change e.inv.app Z ((TensorOpenRestriction318.iso W.ι M N).inv.app Z
      (IntrinsicTensorSheaf318.pure (M.restrict W.ι) (N.restrict W.ι) Z m n))=
      d.inv.app Z ((TensorOpenRestriction318.iso W.ι M N).inv.app Z
        (IntrinsicTensorSheaf318.pure (M.restrict W.ι) (N.restrict W.ι) Z m n))
    rw [OriginalTensorOpenNaturality318.inverse_pure,
      OriginalTensorOpenNaturality318.inverse_pure]
    have hl : W.ι ''ᵁ Z≤W := by simpa using W.ι.image_le_opensRange Z
    change e.inv.app Z (IntrinsicTensorSheaf318.pure M N (W.ι ''ᵁ Z) m n)=
      d.inv.app Z (IntrinsicTensorSheaf318.pure M N (W.ι ''ᵁ Z) m n)
    rw [←LineFrameChartCoordinates318.over_inv_app _ W e Z,
      ←LineFrameChartCoordinates318.over_inv_app _ W d Z]
    change (OpenLineFrameCoordinates318.frame _ W e (W.ι ''ᵁ Z) hl).symm
        (IntrinsicTensorSheaf318.pure M N (W.ι ''ᵁ Z) m n)=
      (OpenLineFrameCoordinates318.frame _ W d (W.ι ''ᵁ Z) hl).symm
        (IntrinsicTensorSheaf318.pure M N (W.ι ''ᵁ Z) m n)
    dsimp only [e,d]
    rw [OpenLineFrameRefinement318.coordinates,TensorLineFrameCoordinates318.inverse_pure,
      TensorLineFrameCoordinates318.inverse_pure,OpenLineFrameRefinement318.coordinates,
      OpenLineFrameRefinement318.coordinates]
  simpa only [Iso.symm_symm_eq] using congrArg Iso.symm hi
end OriginalTensorFrameRefinement318
