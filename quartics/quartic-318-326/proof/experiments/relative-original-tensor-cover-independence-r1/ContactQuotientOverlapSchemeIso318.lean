module
public import ContactQuotientOverlapSchemeRule318
public section
noncomputable section
namespace ContactQuotientOverlapSchemeIso318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientOverlapOpen318 ContactQuotientOverlapSchemeRule318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
lemma inverse_tests (S : CommRingCat.{0}) [Algebra ℚ S]
    (x : RelativeAffineTestRule318.Test ℚ (structureMap c a b n) S) :
    (rule c b a n).app S ((rule c a b n).app S x)=x := by
  apply Subtype.ext
  change (ContactQuotientOverlapPointEquiv318.transition c b a n S
    (ContactQuotientOverlapPointEquiv318.transition c a b n S ((pointTest c a b n S).symm x))).val=x.val
  have h : ContactQuotientOverlapPointEquiv318.transition c b a n S=
      (ContactQuotientOverlapPointEquiv318.transition c a b n S).symm := rfl
  rw [h,Equiv.symm_apply_apply]
  rfl
/-- The overlap transition is now an ACTUAL SCHEME ISOMORPHISM,
constructed from the proved natural operations on all affine tests. -/
@[expose] def iso : scheme c a b n ≅ scheme c b a n :=
  RelativeAffineTestIso318.iso ℚ (structureMap c a b n) (structureMap c b a n)
    (rule c a b n) (rule c b a n) (inverse_tests c a b n) (inverse_tests c b a n)
@[reassoc] lemma over : (iso c a b n).hom ≫ structureMap c b a n=structureMap c a b n :=
  RelativeAffineTestGluing318.over ℚ _ _ _
/-- Its application is the previously constructed EXACT full-ideal
transition, not merely an unspecified representing morphism. -/
@[reassoc] lemma evaluate (S : CommRingCat.{0}) [Algebra ℚ S] (x : Point c a b n S) :
    x.val ≫ (iso c a b n).hom=(ContactQuotientOverlapPointEquiv318.transition c a b n S x).val :=
  RelativeAffineTestEvaluation318.evaluate ℚ _ _ _ S (pointTest c a b n S x)
end ContactQuotientOverlapSchemeIso318
