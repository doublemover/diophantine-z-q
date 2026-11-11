module
public import ContactHilbertLocalIdeal318
public section
noncomputable section
namespace ContactHilbertPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactHilbertData318 ContactQuotientChart318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedRank S c n)
local notation "q" => D.val.ideal.subschemeι
local notation "Db" => ContactHilbertLocalClassifier318.bounded S c n D
/-- Every original finite-flat finitely presented fixed-rank family supplies the exact
whole-cover local presentation required by global parameter gluing. -/
@[expose] def data : ContactProjectiveLocalPresentation318.Data c n S q where
  coefficients := ContactHilbertLocalIdeal318.coefficients S c n D
  chart := ContactHilbertLocalIdeal318.chart S c n D
  ideal := ContactHilbertLocalIdeal318.ideal S c n D
  toFamily a := (ContactHilbertLocalIdeal318.comparison S c n D a).hom ≫
    ContactHilbertAffineWholeFamily318.toFamily S c n Db a
  cartesian a := by
    apply IsPullback.of_iso_pullback (i := ContactHilbertLocalIdeal318.comparison S c n D a)
    · constructor
      rw [Category.assoc,pullback.condition,← Category.assoc,ContactHilbertLocalIdeal318.comparison_into]
    · rfl
    · exact ContactHilbertLocalIdeal318.comparison_into S c n D a
end ContactHilbertPresentation318
