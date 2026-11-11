module
public import ContactQuotientChart318
public section
noncomputable section
namespace ContactQuotientChartTransfer318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n)
/-- The whole original quotient, including its full scheme structure,
is supported in the other original affine chart. -/
@[expose] def Supported : Prop := Set.range (projectiveInto c a S n I) ⊆ Set.range (into c b S)
variable (h : Supported c a b S n I)
@[expose] def lift : family c a S n I ⟶ Spec (CommRingCat.of (S ⊗[ℚ] ring c b)) :=
  IsOpenImmersion.lift (into c b S) (projectiveInto c a S n I) h
instance closed : IsClosedImmersion (lift c a b S n I h) := ClosedImmersionOpenLift318.closed _ _ _
@[reassoc] lemma lift_into : lift c a b S n I h ≫ into c b S=projectiveInto c a S n I :=
  IsOpenImmersion.lift_fac _ _ _
@[reassoc] lemma lift_projection : lift c a b S n I h ≫
    VaryingSourceCoefficientPullback318.projection ℚ (ring c b) S=projection c a S n I := by
  rw [← ContactRelativeLinearOpenChart318.over_test,← Category.assoc,lift_into]
  exact ContactAffineQuotientToProjective318.into_projection S c a.form a.homogeneous n I
instance finite : IsFinite (AffineWholeQuotientProjection318.projection ℚ (ring c b) S (lift c a b S n I h)) := by
  change IsFinite (lift c a b S n I h ≫ _)
  rw [lift_projection]
  exact ContactAffineQuotientToProjective318.finite S c a.form a.homogeneous n I
instance flat : Flat (AffineWholeQuotientProjection318.projection ℚ (ring c b) S (lift c a b S n I h)) := by
  change Flat (lift c a b S n I h ≫ _)
  rw [lift_projection]
  exact ContactAffineQuotientToProjective318.flat S c a.form a.homogeneous n I
instance presentation : LocallyOfFinitePresentation
    (AffineWholeQuotientProjection318.projection ℚ (ring c b) S (lift c a b S n I h)) := by
  change LocallyOfFinitePresentation (lift c a b S n I h ≫ _)
  rw [lift_projection]
  infer_instance
lemma rank (x : PrimeSpectrum S) :
    (AffineWholeQuotientProjection318.projection ℚ (ring c b) S (lift c a b S n I h)).finrank x=
      Fintype.card (Fin n) := by
  change (lift c a b S n I h ≫ _).finrank x=_
  rw [lift_projection]
  exact ContactQuotientChart318.rank c a S n I x
/-- Genuine full-ideal reclassification in the other source chart. -/
@[expose] def transfer : Ideal c b S n :=
  AffineFiniteProjectiveQuotient318.data ℚ (ring c b) S (lift c a b S n I h) (Fin n)
    (rank c a b S n I h)
@[expose] def comparison : family c a S n I ≅ family c b S n (transfer c a b S n I h) :=
  AffineClosedQuotientExtraction318.comparison (S ⊗[ℚ] ring c b) (lift c a b S n I h)
@[reassoc] lemma comparison_quotient : (comparison c a b S n I h).hom ≫
    quotientInto c b S n (transfer c a b S n I h)=lift c a b S n I h :=
  AffineClosedQuotientExtraction318.comparison_into _ _
@[reassoc] lemma comparison_projective : (comparison c a b S n I h).hom ≫
    projectiveInto c b S n (transfer c a b S n I h)=projectiveInto c a S n I := by
  change (comparison c a b S n I h).hom ≫ (quotientInto c b S n (transfer c a b S n I h) ≫ into c b S)=_
  rw [← Category.assoc,comparison_quotient,lift_into]
@[reassoc] lemma inverse_projective : (comparison c a b S n I h).inv ≫ projectiveInto c a S n I=
    projectiveInto c b S n (transfer c a b S n I h) := by
  rw [← comparison_projective,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
end ContactQuotientChartTransfer318
