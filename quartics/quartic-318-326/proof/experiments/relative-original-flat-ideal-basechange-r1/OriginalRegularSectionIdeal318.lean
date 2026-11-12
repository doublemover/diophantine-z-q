module
public import RegularSectionFlatExtension318
public import OriginalAffineRegularOpenPullback318
public import OriginalRegularIdealCover318
public section
noncomputable section
namespace OriginalRegularSectionIdeal318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : CommRingCat.{u}) (L : Line (Spec A))
  (s : OriginalLineAffineModel318.sections A L)
  (hs : SectionZeroRegularCoordinate318.Regular A (OriginalLineAffineModel318.sections A L) s)

/-- The SAME intrinsic original section, restricted to any genuine
original affine open, remains regular through its actual comparison unit.
Unlike a frame argument, this does not assume the whole affine line free. -/
lemma open_regular (B : CommRingCat.{u}) (f : A ⟶ B) [IsOpenImmersion (Spec.map f)] :
    SectionZeroRegularCoordinate318.Regular B
      (OriginalLineAffineModel318.sections B (LineSheafPullback318.line (Spec.map f) L))
      (OriginalAffineLinePathSections318.restriction f L
        (LineSheafPullback318.line (Spec.map f) L) (Iso.refl _) s) := by
  letI : Algebra A B := f.hom.toAlgebra
  letI : Module.Flat A B := OriginalAffineRegularOpenPullback318.scalar_flat A B f
  let N := LineSheafPullback318.line (Spec.map f) L
  let e := (OriginalAffineLinePathSections318.comparison f L N (Iso.refl _)).toLinearEquiv
  have hu : e ((1:B) ⊗ₜ[A] s)=OriginalAffineLinePathSections318.restriction f L N (Iso.refl _) s :=
    OriginalAffineLinePathSections318.unit_apply f L N (Iso.refl _) s
  rw [← hu]
  exact RegularSectionFlatExtension318.regular A B _ _ s hs e

/-- Genuine principal nonzerodivisor charts for the literal original
section ideal. Actual affine principal frames cover the entire target;
the ideal is transported by the original restriction path, not radicalized. -/
lemma property : OriginalRegularIdealCover318.Property A (OriginalAffineSectionZero318.ideal A L s) := by
  intro x
  obtain ⟨r,y,hy⟩ := OriginalPrincipalAffineFrames318.covers A L x
  let B := OriginalPrincipalAffineFrames318.ring A L r
  let f := OriginalPrincipalAffineFrames318.arrow A L r
  let N := LineSheafPullback318.line (Spec.map f) L
  let t := OriginalAffineLinePathSections318.restriction f L N (Iso.refl _) s
  let e := OriginalPrincipalAffineFrames318.frame A L r
  refine ⟨B,f,inferInstance,⟨y,hy⟩,e t,?_,?_⟩
  · exact (OriginalAffineSectionZero318.along_path f L N (Iso.refl _) s).symm.trans
      (SectionZeroRegularCoordinate318.ideal_in_frame B _ t e)
  · exact (SectionZeroRegularCoordinate318.regular_iff B _ t e).mp
      (open_regular A L s hs B f)
end OriginalRegularSectionIdeal318
