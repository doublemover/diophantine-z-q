module
public import ClosedPullbackKernel318
public section
noncomputable section
namespace ContactSchemePointTest318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (f : ContactSchemePointFamily318.SchemePoint c n b)
  (S : CommRingCat.{0}) [Algebra ℚ S] (x : RelativeAffineTestRule318.Test ℚ b S)
@[expose] def point : ContactProjectiveParameterPoint318.Point c n S :=
  ⟨x.val ≫ f.val,by rw [Category.assoc,f.property]; exact x.property⟩
lemma extracted_ideal : (ContactSchemeHilbertTest318.data c n b
    (ContactSchemePointFamily318.extract c n b f) S x).val.ideal=
      ContactProjectivePointFamily318.idealSheaf c n S (point c n b f S x) := by
  have hg := ClosedPullbackKernel318.ideal _ _ _ _ (ContactSchemePointFamily318.cartesian c n b f)
  have hl := ClosedPullbackKernel318.ideal _ _ _ _ (ContactProjectivePointFamily318.cartesian c n S (point c n b f S x))
  change (ContactSchemePointFamily318.into c n b f).ker.comap
    (ContactSchemeHilbertTest318.sourceMap c b S x)=_
  rw [hg,← Scheme.IdealSheafData.comap_comp,RelativeSchemeCoefficient318.comp]
  exact hl.symm
lemma classify_test : ContactHilbertFixedRankEquiv318.equivalence c n S
    (ContactSchemeHilbertTest318.data c n b (ContactSchemePointFamily318.extract c n b f) S x)=
      point c n b f S x := by
  let E := ContactHilbertFixedRankEquiv318.equivalence c n S
  have hi : (E.symm (point c n b f S x)).val.ideal=
      ContactProjectivePointFamily318.idealSheaf c n S (point c n b f S x) := by
    have h := ContactHilbertFixedRankEquiv318.full_ideal_recovery c n S (E.symm (point c n b f S x))
    rw [E.apply_symm_apply] at h
    exact h.symm
  have hD : ContactSchemeHilbertTest318.data c n b (ContactSchemePointFamily318.extract c n b f) S x=
      E.symm (point c n b f S x) := by
    apply Subtype.ext
    apply ContactHilbertData318.Datum.ext
    exact (extracted_ideal c n b f S x).trans hi.symm
  exact (congrArg E hD).trans (E.apply_symm_apply _)
end ContactSchemePointTest318
