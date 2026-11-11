module
public import ContactFixedDegreeLocalIdeal318
public section
noncomputable section
namespace ContactFixedDegreePresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveDegreeData318 ContactQuotientChart318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedDegree S c n)
local notation "q" => ContactProjectiveQuotientGluing318.into S c D.val.datum
local notation "Db" => ContactFixedDegreeLocalClassifier318.bounded S c n D
/-- Every original effective fixed-degree family supplies the exact
whole-cover local presentation required by global parameter gluing. -/
@[expose] def data : ContactProjectiveLocalPresentation318.Data c n S q where
  coefficients := ContactFixedDegreeLocalIdeal318.coefficients S c n D
  chart := ContactFixedDegreeLocalIdeal318.chart S c n D
  ideal := ContactFixedDegreeLocalIdeal318.ideal S c n D
  toFamily a := (ContactFixedDegreeLocalIdeal318.comparison S c n D a).hom ≫
    ContactAvoidanceAffineWholeFamily318.toFamily S c n Db a
  cartesian a := by
    apply IsPullback.of_iso_pullback (i := ContactFixedDegreeLocalIdeal318.comparison S c n D a)
    · constructor
      rw [Category.assoc,pullback.condition,← Category.assoc,ContactFixedDegreeLocalIdeal318.comparison_into]
    · rfl
    · exact ContactFixedDegreeLocalIdeal318.comparison_into S c n D a
end ContactFixedDegreePresentation318
