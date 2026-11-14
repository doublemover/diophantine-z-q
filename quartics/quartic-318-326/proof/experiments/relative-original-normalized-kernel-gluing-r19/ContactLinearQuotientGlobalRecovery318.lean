module
public import ContactAffineQuotientToProjective318
public import ContactProjectiveClosedRecovery318
public section
noncomputable section
namespace ContactLinearQuotientGlobalRecovery318
open AlgebraicGeometry CategoryTheory
open VaryingProjectiveQuotientEquiv318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ)
  (l : MvPolynomial (Fin 2) ℚ) (hl : l∈ProjectiveJLine318.grading ℚ 1)
  (n : ℕ)
local notation "A" => ContactOriginalLinearOpenChart318.ring c l hl
variable (I : ProjectiveIdeal ℚ A (Fin n) S)
local notation "q" => ContactAffineQuotientToProjective318.into S c l hl n I
/-- Full finite/infinity ideals on the original projective model are
extracted from the actual closed quotient, without assuming that each
original chart restriction is finite over the coefficient base. -/
@[expose] def datum : ContactProjectiveQuotientData318.Datum S c :=
  ContactProjectiveClosedData318.datum S c q
@[expose] def comparison : ContactProjectiveQuotientGluing318.family S c (datum S c l hl n I) ≅
    ContactAffineQuotientToProjective318.family S c l hl n I :=
  ContactProjectiveClosedRecovery318.comparison S c q
@[reassoc] lemma comparison_into : (comparison S c l hl n I).hom ≫ q=
    ContactProjectiveQuotientGluing318.into S c (datum S c l hl n I) :=
  ContactProjectiveClosedRecovery318.forward_into S c q
lemma full_ideal : ContactProjectiveQuotientIdealSheaf318.idealSheaf S c (datum S c l hl n I)=q.ker :=
  ContactProjectiveClosedRecovery318.idealSheaf_eq S c q
@[reassoc] lemma comparison_projection : (comparison S c l hl n I).hom ≫
    ContactAffineQuotientToProjective318.projection S c l hl n I=
      ContactProjectiveQuotientGluing318.projection S c (datum S c l hl n I) := by
  rw [← ContactAffineQuotientToProjective318.into_projection,← Category.assoc,comparison_into]
  rfl
instance finite : IsFinite (ContactProjectiveQuotientGluing318.projection S c (datum S c l hl n I)) := by
  rw [← comparison_projection]
  infer_instance
instance flat : Flat (ContactProjectiveQuotientGluing318.projection S c (datum S c l hl n I)) := by
  rw [← comparison_projection]
  infer_instance
end ContactLinearQuotientGlobalRecovery318
