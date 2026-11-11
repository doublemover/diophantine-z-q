module
public import DualThickeningIso318
public section
noncomputable section
namespace OriginalAffineThickeningFrames318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ DualNumberScheme318.base R) (L : DualNumberScheme318.Deformation R p)
/-- EVERY actual affine original scheme, including the empty affine scheme,
has trivial pointed dual-number lines. The map to Spec R is not assumed to
be a predefined algebraMap: it is obtained from the actual original morphism. -/
lemma exists_frame : Nonempty (SheafOfModules.unit (DualNumberScheme318.thickening R p).ringCatSheaf ≅
    L.line.object) := by
  obtain ⟨f,hf⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  let S := Γ(X, ⊤)
  letI : Algebra R S := f.hom.toAlgebra
  have he : X.isoSpec.hom ≫ RelativeAffineDualPresentation318.baseMap R S = p := by
    change X.isoSpec.hom ≫ Spec.map f = p
    rw [hf, Iso.hom_inv_id_assoc]
  let M := DualThickeningIso318.transport R p (RelativeAffineDualPresentation318.baseMap R S)
    X.isoSpec he L
  exact ⟨DualThickeningIso318.frameOfTransport R p (RelativeAffineDualPresentation318.baseMap R S)
    X.isoSpec he L (RelativeAffinePointedTriviality318.frame R S M)⟩
@[expose] def frame : SheafOfModules.unit (DualNumberScheme318.thickening R p).ringCatSheaf ≅
    L.line.object := (exists_frame R p L).some
@[expose] def pointedIso : PointedLineDeformation318.PointedIso
    (DualNumberScheme318.reduction R p) L
    (PointedLineDeformation318.trivial (DualNumberScheme318.reduction R p)) :=
  SplitReductionPointedKernel318.pointedIsoOfIso _
    (pullback.fst p (DualNumberScheme318.structureMap R))
    (DualNumberScheme318.reduction_fst R p) L _ (frame R p L).symm
lemma class_trivial : PointedLineDeformation318.classOf _ L =
    PointedLineDeformation318.classOf _
      (PointedLineDeformation318.trivial (DualNumberScheme318.reduction R p)) :=
  (PointedLineDeformation318.classOf_eq_iff _ _ _).2 ⟨pointedIso R p L⟩
instance pointed_subsingleton : Subsingleton (DualNumberScheme318.Class R p) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M => exact (class_trivial R p L).trans (class_trivial R p M).symm
end OriginalAffineThickeningFrames318
