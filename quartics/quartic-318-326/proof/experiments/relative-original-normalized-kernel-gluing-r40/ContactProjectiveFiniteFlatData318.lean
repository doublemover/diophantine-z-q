module
public import ContactProjectiveIdealSheafEquiv318
public import ContactProjectiveQuotientProperties318
public section
noncomputable section
namespace ContactProjectiveFiniteFlatData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
@[expose] def FiniteFlatDatum := {D : Datum R c //
  IsFinite (ContactProjectiveQuotientGluing318.projection R c D) ∧
  Flat (ContactProjectiveQuotientGluing318.projection R c D)}
variable {Z : Scheme.{0}} (p : Z ⟶ ContactOriginalRelativePolynomialCharts318.curve R c) [IsClosedImmersion p]
local notation "D" => ContactProjectiveClosedData318.datum R c p
local notation "π" => ContactRelativeStructuralHOne318.projection R c
@[reassoc] lemma comparison_projection : (ContactProjectiveClosedRecovery318.comparison R c p).hom ≫
    (p ≫ π)=ContactProjectiveQuotientGluing318.projection R c D := by
  change ContactProjectiveClosedRecovery318.forward R c p ≫ (p ≫ π)=_
  rw [← Category.assoc,ContactProjectiveClosedRecovery318.forward_into]
  rfl
/-- EVERY actual finite-flat closed projective family supplies compatible
full chart ideals in the correct image. No individual affine chart
quotient is assumed finite or globally free over the base. -/
@[expose] def ofClosed [IsFinite (p ≫ π)] [Flat (p ≫ π)] : FiniteFlatDatum R c := by
  refine ⟨D,?_,?_⟩
  · rw [← comparison_projection]
    infer_instance
  · rw [← comparison_projection]
    infer_instance
lemma recovers_original [IsFinite (p ≫ π)] [Flat (p ≫ π)] :
    Nonempty (ContactProjectiveQuotientGluing318.family R c (ofClosed R c p).val ≅ Z) :=
  ⟨ContactProjectiveClosedRecovery318.comparison R c p⟩
end ContactProjectiveFiniteFlatData318
