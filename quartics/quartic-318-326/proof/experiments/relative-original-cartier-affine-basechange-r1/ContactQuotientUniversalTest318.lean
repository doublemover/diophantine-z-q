module
public import ContactQuotientUniversalOriginal318
public section
noncomputable section
namespace ContactQuotientUniversalTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (a : Chart) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  (I : Ideal c a S n)
local notation "A" => ring c a
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactQuotientUniversalOriginal318.structureMap c a n
local notation "x" => VaryingProjectiveQuotientEquiv318.equivalence ℚ A (Fin n) S I
/-- The actual whole affine quotient comparison, retaining the universal
family map as well as its original projective closed insertion. -/
abbrev toFamily : family c a S n I ⟶ ContactQuotientUniversalOriginal318.family c a n :=
  (VaryingProjectiveQuotientFamily318.comparison ℚ A (Fin n) S I).hom ≫
    VaryingParameterPointFamily318.intoFamily ℚ A (Fin n) S x
abbrev baseInto : ContactRelativeLinearOpenChart318.curve S c ⟶
    ContactQuotientUniversalOriginal318.curve c a n :=
  RelativeSchemeCoefficient318.map p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property
@[reassoc] lemma toFamily_base : toFamily c a n S I ≫ ContactQuotientUniversalOriginal318.projection c a n=
    projection c a S n I ≫ x.val := (VaryingProjectiveQuotientFamily318.cartesian ℚ A (Fin n) S I).w
@[reassoc] lemma toFamily_original : toFamily c a n S I ≫ VaryingWordGlobalOriginalMap318.original ℚ A (Fin n)=
    quotientInto c a S n I ≫ VaryingSourceCoefficientPullback318.original ℚ A S := by
  rw [toFamily,Category.assoc,← VaryingParameterPointFamily318.into_original,
    ← Category.assoc,VaryingProjectiveQuotientFamily318.comparison_into]
@[reassoc] lemma literal_original : projectiveInto c a S n I ≫
    pullback.fst p (VaryingSourceCoefficientPullback318.base ℚ S)=
      quotientInto c a S n I ≫ VaryingSourceCoefficientPullback318.original ℚ A S ≫ original c a := by
  change (quotientInto c a S n I ≫ ContactRelativeLinearOpenChart318.into S c a.form a.homogeneous) ≫ _=_
  rw [Category.assoc,RelativeOriginalAffineChart318.over_original]
lemma source_square : toFamily c a n S I ≫ ContactQuotientUniversalOriginal318.into c a n=
    projectiveInto c a S n I ≫ baseInto c a n S I := by
  apply pullback.hom_ext
  · rw [Category.assoc,ContactQuotientUniversalOriginal318.into_original,← Category.assoc,toFamily_original,
      Category.assoc,Category.assoc,RelativeSchemeCoefficient318.map_fst,literal_original]
  · rw [Category.assoc,ContactQuotientUniversalOriginal318.into_base,toFamily_base,
      Category.assoc,RelativeSchemeCoefficient318.map_snd,← Category.assoc,
      ContactAffineQuotientToProjective318.into_projection]
/-- Every literal full ideal is recovered by the actual universal
original CLOSED family, not merely by its module or reduced support. -/
lemma cartesian : IsPullback (toFamily c a n S I) (projectiveInto c a S n I)
    (ContactQuotientUniversalOriginal318.into c a n) (baseInto c a n S I) := by
  apply IsPullback.of_bot (v₂₁ := ContactRelativeLinearOpenChart318.projection S c)
    (v₂₂ := pullback.snd p b)
  · simpa only [ContactQuotientUniversalOriginal318.into_base,
      ContactAffineQuotientToProjective318.into_projection] using
        VaryingProjectiveQuotientFamily318.cartesian ℚ A (Fin n) S I
  · exact source_square c a n S I
  · exact RelativeSchemeCoefficient318.cartesian p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property
end ContactQuotientUniversalTest318
