module
public import ContactProjectiveLocalAgreement318
public section
noncomputable section
namespace ContactProjectiveGlobalClassifyingMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveLocalPresentation318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
  (D : Data c n S q)
local notation "C" => D.coefficients
local notation "U" => AffineCoefficientCover318.cover ℚ S C
lemma compatible (i j : C.Index) : pullback.fst (U.f i) (U.f j) ≫ (localPoint c n S q D i).val=
    pullback.snd (U.f i) (U.f j) ≫ (localPoint c n S q D j).val := by
  let V := (pullback (U.f i) (U.f j)).affineOpenCover
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro k
  have h := ContactProjectiveLocalAgreement318.agreement c n S q D i j
    (AffineCoefficientOverlapTests318.ring ℚ S C i j k)
    (AffineCoefficientOverlapTests318.leftHom ℚ S C i j k)
    (AffineCoefficientOverlapTests318.rightHom ℚ S C i j k)
    (AffineCoefficientOverlapTests318.hom_comp ℚ S C i j k)
  rw [AffineCoefficientOverlapTests318.left_spec,AffineCoefficientOverlapTests318.right_spec] at h
  simpa only [AffineCoefficientOverlapTests318.left,AffineCoefficientOverlapTests318.right,Category.assoc] using h
/-- The local original-family classifiers genuinely glue over their
whole coefficient cover to the actual projective parameter scheme. -/
@[expose] def classify : Spec S ⟶ ContactProjectiveQuotientParameter318.scheme c n :=
  U.glueMorphisms (fun i => (localPoint c n S q D i).val) (compatible c n S q D)
@[reassoc] lemma local_classify (i : C.Index) : U.f i ≫ classify c n S q D=(localPoint c n S q D i).val :=
  U.ι_glueMorphisms _ _ i
@[reassoc] lemma over : classify c n S q D ≫ ContactProjectiveParameterStructure318.structureMap c n=
    VaryingSourceCoefficientPullback318.base ℚ S := by
  apply Scheme.Cover.hom_ext U _ _
  intro i
  rw [← Category.assoc,local_classify]
  exact (localPoint c n S q D i).property.trans (AffineCoefficientCover318.over_base ℚ S C i).symm
@[expose] def point : ContactProjectiveParameterPoint318.Point c n S := ⟨classify c n S q D,over c n S q D⟩
end ContactProjectiveGlobalClassifyingMap318
