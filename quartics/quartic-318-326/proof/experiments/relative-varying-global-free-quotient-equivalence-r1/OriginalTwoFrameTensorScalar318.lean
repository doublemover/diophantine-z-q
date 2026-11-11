module
public import OriginalTensorUntwistRefinement318
public import OriginalRestrictedFrameScalar318
public section
noncomputable section
namespace OriginalTwoFrameTensorScalar318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L N : Line X) (U V : X.Opens)
  (e : N.object.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
  (f : N.object.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
  (a : Γ(X,U ⊓ V)ˣ)
  (h : ∀ s : Γ(N.object,U ⊓ V),
    (OpenLineFrameCoordinates318.frame N.object U e.symm _ inf_le_left).symm s =
    (OpenLineFrameCoordinates318.frame N.object V f.symm _ inf_le_right).symm s * a.val)

include h in
/-- Actual tensor untwisting on the whole intersection changes by the
specified original regular transition, with no global-section generation
or field hypothesis. -/
lemma scalar_square (s : Γ((LineSheafTensor318.line L N).object,U ⊓ V)) :
    OriginalTensorUntwistOver318.sections L N U e (U ⊓ V) inf_le_left s =
      a.val • OriginalTensorUntwistOver318.sections L N V f (U ⊓ V) inf_le_right s := by
  let W := U ⊓ V
  let ef := (OpenLineFrameRefinement318.frame N.object U e.symm W inf_le_left).symm
  let ff := (OpenLineFrameRefinement318.frame N.object V f.symm W inf_le_right).symm
  let t := (OriginalRestrictionTopScalar318.moduleTop (LineSheafTensor318.line L N).object W).symm s
  have hc : (OriginalTensorLineChartUntwist318.iso L N W ef).hom =
      (OriginalTensorLineChartUntwist318.iso L N W ff).hom ≫
        ModuleScalar318.map (L.object.restrict W.ι) ((LineFrameTopScalar318.ringTop W).inv a.val) := by
    have hz := OriginalRestrictedFrameScalar318.tensor_change N.object U V W
      inf_le_left inf_le_right e.symm f.symm (L.object.restrict W.ι) a h
    have hz' := congrArg (fun q => (TensorOpenRestriction318.iso W.ι L.object N.object).hom ≫ q) hz
    simpa only [OriginalTensorLineChartUntwist318.iso,OriginalTensorFrameChange318.iso,
      OriginalRestrictedFrameScalar318.leftFrame,OriginalRestrictedFrameScalar318.rightFrame,
      Iso.trans_hom,Category.assoc,ef,ff] using hz'
  have hm := congrArg (fun q => OriginalRestrictionTopScalar318.moduleTop L.object W (q.app ⊤ t)) hc
  change OriginalRestrictionTopScalar318.moduleTop L.object W
      ((OriginalTensorLineChartUntwist318.iso L N W ef).hom.app ⊤ t) =
    OriginalRestrictionTopScalar318.moduleTop L.object W
      ((ModuleScalar318.map (L.object.restrict W.ι) ((LineFrameTopScalar318.ringTop W).inv a.val)).app ⊤
        ((OriginalTensorLineChartUntwist318.iso L N W ff).hom.app ⊤ t)) at hm
  rw [OriginalRestrictionTopScalar318.multiply,Iso.inv_hom_id_apply] at hm
  have hf := OriginalTensorUntwistOver318.top_square L N W ef t
  have hi := OriginalTensorUntwistOver318.top_square L N W ff t
  have ht : OriginalRestrictionTopScalar318.moduleTop (LineSheafTensor318.line L N).object W t = s :=
    AddEquiv.apply_symm_apply _ s
  rw [ht] at hf hi
  have hf' := OriginalTensorUntwistRefinement318.sections L N U e W inf_le_left W le_rfl s
  have hi' := OriginalTensorUntwistRefinement318.sections L N V f W inf_le_right W le_rfl s
  exact hf'.trans (hf.trans (hm.trans (congrArg (fun y => a.val • y) (hi.symm.trans hi'.symm))))
end OriginalTwoFrameTensorScalar318
