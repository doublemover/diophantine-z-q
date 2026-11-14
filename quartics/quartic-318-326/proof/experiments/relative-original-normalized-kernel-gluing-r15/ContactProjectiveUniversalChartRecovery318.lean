module
public import ContactProjectiveUniversalProjection318
public section
noncomputable section
namespace ContactProjectiveUniversalChartRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (a : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (I : Ideal c a S n)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactProjectiveParameterStructure318.structureMap c n
local notation "x" => ContactProjectiveParameterPoint318.ofIdeal c n S a I
abbrev toFamily : family c a S n I ⟶ ContactProjectiveUniversalGluing318.family c n :=
  ContactQuotientUniversalTest318.toFamily c a n S I ≫ ContactProjectiveUniversalGluing318.into c n a
abbrev sourceMap : ContactRelativeLinearOpenChart318.curve S c ⟶ ContactProjectiveUniversalAmbient318.scheme c n :=
  RelativeSchemeCoefficient318.map p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property
/-- The actual literal original quotient is recovered as a Cartesian
closed family over its point in the GLOBAL projective parameter, not only
in the affine-source parameter chart. -/
lemma source_cartesian : IsPullback (toFamily c n a S I) (projectiveInto c a S n I)
    (ContactProjectiveUniversalGluing318.original c n) (sourceMap c n a S I) := by
  have h := (ContactQuotientUniversalTest318.cartesian c a n S I).paste_horiz
    (ContactProjectiveUniversalGluing318.cartesian c n a)
  simpa only [ContactQuotientUniversalTest318.baseInto,ContactProjectiveUniversalAmbient318.into,
    RelativeSchemeCoefficient318.comp] using h
lemma cartesian : IsPullback (toFamily c n a S I) (projection c a S n I)
    (ContactProjectiveUniversalProjection318.projection c n) x.val := by
  have h := (VaryingProjectiveQuotientFamily318.cartesian ℚ (ring c a) (Fin n) S I).paste_horiz
    (ContactProjectiveUniversalProjection318.cartesian c n a)
  exact h
end ContactProjectiveUniversalChartRecovery318
