module
public import ContactSectionQuotientComparison318
public import ContactFieldGlobalZeroFinite318
public section
noncomputable section
namespace ContactSectionQuotientProperties318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (ContactOriginalRelativePolynomialCharts318.curve R c)) (s : Γ(L.object,⊤))
local notation "D" => ContactSectionQuotientData318.datum R c L s
local notation "e" => ContactSectionQuotientComparison318.comparison R c L s
/-- The new arbitrary-ideal construction recovers the whole OLD section
ideal sheaf, not merely the closed support or its geometric fibers. -/
lemma idealSheaf_eq : ContactProjectiveQuotientIdealSheaf318.idealSheaf R c D=
    ContactGlobalZeroClosed318.idealSheaf R c L s := by
  have h := Scheme.Hom.ker_comp_of_isIso e.hom (ContactGlobalSectionZero318.into R c L s)
  change (ContactSectionQuotientComparison318.forward R c L s ≫
    ContactGlobalSectionZero318.into R c L s).ker=_ at h
  rw [ContactSectionQuotientComparison318.forward_into] at h
  exact h
@[reassoc] lemma comparison_projection : e.hom ≫ ContactGlobalResidueFlat318.projection R c L s=
    ContactProjectiveQuotientGluing318.projection R c D := by
  change ContactSectionQuotientComparison318.forward R c L s ≫
    (ContactGlobalSectionZero318.into R c L s ≫ ContactRelativeStructuralHOne318.projection R c)=_
  rw [← Category.assoc,ContactSectionQuotientComparison318.forward_into]
  rfl
lemma flat (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s) :
    Flat (ContactProjectiveQuotientGluing318.projection R c D) := by
  letI := ContactGlobalResidueFlat318.flat R c L s hs
  rw [← comparison_projection]
  infer_instance
/-- Over a field, the same nonzero-section family is finite. This uses
actual global properness and retains multiplicities, not local finiteness
of arbitrary open restrictions over a general coefficient ring. -/
lemma finite [Field R] (hs : s≠0) :
    IsFinite (ContactProjectiveQuotientGluing318.projection R c D) := by
  letI := ContactFieldGlobalZeroFinite318.finite R c L s hs
  rw [← comparison_projection]
  infer_instance
end ContactSectionQuotientProperties318
