module
public import OriginalTensorFrameChange318
public import LineFrameTopScalar318
public import OpenLineFrameRefinement318
public section
noncomputable section
namespace OriginalRestrictedFrameScalar318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (N : X.Modules) (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι)
  (f : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ N.restrict V.ι)

def leftFrame := OpenLineFrameRefinement318.frame N U e W hU
def rightFrame := OpenLineFrameRefinement318.frame N V f W hV

/-- The actual regular transition on W determines the actual refined
frame scalar; this uses the original restriction coherence, not new frames. -/
lemma ambient_scalar (a : Γ(X,W)ˣ)
    (h : ∀ s : Γ(N,W),
      (OpenLineFrameCoordinates318.frame N U e W hU).symm s =
      (OpenLineFrameCoordinates318.frame N V f W hV).symm s * a.val) :
    FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame N W (leftFrame N U W hU e) W le_rfl)
      (OpenLineFrameCoordinates318.frame N W (rightFrame N V W hV f) W le_rfl) = a := by
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame N W (leftFrame N U W hU e) W le_rfl).symm
    (OpenLineFrameCoordinates318.frame N W (rightFrame N V W hV f) W le_rfl 1) = a.val
  simp only [leftFrame,rightFrame,OpenLineFrameRefinement318.coordinates]
  rw [h,LinearEquiv.symm_apply_apply,one_mul]

/-- The SAME refined frame change on the open subscheme has the exact
original ambient scalar transported by the canonical original ringTop iso. -/
lemma unit_value (a : Γ(X,W)ˣ)
    (h : ∀ s : Γ(N,W),
      (OpenLineFrameCoordinates318.frame N U e W hU).symm s =
      (OpenLineFrameCoordinates318.frame N V f W hV).symm s * a.val) :
    (UnitSheafScalar318.unit
      (rightFrame N V W hV f ≪≫ (leftFrame N U W hU e).symm)).val =
        (LineFrameTopScalar318.ringTop W).inv a.val := by
  have he := LineFrameTopScalar318.scalar N W (leftFrame N U W hU e) (rightFrame N V W hV f)
  rw [ambient_scalar N U V W hU hV e f a h] at he
  have hv := congrArg Units.val he
  have hi := congrArg (fun x => (LineFrameTopScalar318.ringTop W).inv x) hv
  change (LineFrameTopScalar318.ringTop W).inv
    ((LineFrameTopScalar318.ringTop W).hom
      (UnitSheafScalar318.unit (rightFrame N V W hV f ≪≫ (leftFrame N U W hU e).symm)).val) =
        (LineFrameTopScalar318.ringTop W).inv a.val at hi
  simpa only [Iso.hom_inv_id_apply] using hi

/-- Original coefficient equality gives equality of the entire actual
refined frame maps, not only their global-section values. -/
lemma frame_change (a : Γ(X,W)ˣ)
    (h : ∀ s : Γ(N,W),
      (OpenLineFrameCoordinates318.frame N U e W hU).symm s =
      (OpenLineFrameCoordinates318.frame N V f W hV).symm s * a.val) :
    (leftFrame N U W hU e).inv = (rightFrame N V W hV f).inv ≫
      ModuleScalar318.map (SheafOfModules.unit W.toScheme.ringCatSheaf)
        ((LineFrameTopScalar318.ringTop W).inv a.val) := by
  have he := UnitSheafScalar318.hom_multiply
    (rightFrame N V W hV f ≪≫ (leftFrame N U W hU e).symm)
  rw [unit_value N U V W hU hV e f a h,← ModuleScalar318.unit_eq] at he
  apply (cancel_epi ((rightFrame N V W hV f).hom)).mp
  simpa only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc] using he

/-- The original tensor comparison on the whole common open changes by
EXACTLY the original regular scalar. The scalar equation is derived from
the supplied actual frame coefficients and the original unit-sheaf theorem. -/
lemma tensor_change (M : W.toScheme.Modules) (a : Γ(X,W)ˣ)
    (h : ∀ s : Γ(N,W),
      (OpenLineFrameCoordinates318.frame N U e W hU).symm s =
      (OpenLineFrameCoordinates318.frame N V f W hV).symm s * a.val) :
    (OriginalTensorFrameChange318.iso M (N.restrict W.ι) (leftFrame N U W hU e).symm).hom =
    (OriginalTensorFrameChange318.iso M (N.restrict W.ι) (rightFrame N V W hV f).symm).hom ≫
      ModuleScalar318.map M ((LineFrameTopScalar318.ringTop W).inv a.val) :=
  OriginalTensorFrameChange318.scalar_change M (N.restrict W.ι) _ _ _
    (frame_change N U V W hU hV e f a h)
end OriginalRestrictedFrameScalar318
