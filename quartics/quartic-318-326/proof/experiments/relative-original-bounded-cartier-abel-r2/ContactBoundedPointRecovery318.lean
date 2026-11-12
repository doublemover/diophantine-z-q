module
public import ContactBoundedPointRestriction318
public section
noncomputable section
namespace ContactBoundedPointRecovery318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (f : ContactBoundedPointFamily318.SchemePoint c N b)
local notation "E" => ContactBoundedPointFamily318.extract c N b f
/-- The actual bounded parameter map is recovered on every coefficient
scheme, including arbitrary disconnected and nonreduced schemes. -/
lemma recover : ContactBoundedInputLocalRecovery318.point c N b E=f := by
  apply Subtype.ext
  apply (ContactBoundedRankCover318.cover c N b E).hom_ext
  intro d
  change (ContactBoundedRankCover318.cover c N b E).f d ≫ ContactBoundedClassifyingMap318.classify c N b E=_
  rw [ContactBoundedClassifyingMap318.evaluate]
  change (ContactBoundedRankData318.point c N b E d).val ≫ ContactBoundedHilbertParameter318.into c N d=_
  rw [ContactBoundedPointRestriction318.point]
  exact ContactBoundedPointRank318.factor_into c N b f d
end ContactBoundedPointRecovery318
