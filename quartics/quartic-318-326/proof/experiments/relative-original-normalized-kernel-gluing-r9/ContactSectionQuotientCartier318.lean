module
public import ContactProjectiveQuotientCartier318
public import ContactSectionQuotientProperties318
public import ContactResidueCartierCharts318
public section
noncomputable section
namespace ContactSectionQuotientCartier318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (ContactOriginalRelativePolynomialCharts318.curve R c)) (s : Γ(L.object,⊤))
  (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s)
local notation "D" => ContactSectionQuotientData318.datum R c L s
lemma finite_regular : OriginalRegularIdealCover318.Property
    (CommRingCat.of (ContactProjectiveQuotientData318.finiteRing R c)) D.finiteIdeal :=
  OriginalRegularSectionIdeal318.property _
    (LineSheafPullback318.line (ContactOriginalRelativePolynomialCharts318.finiteInto R c) L) _
    (ContactResidueSectionRegular318.finite_regular R c L s hs)
lemma infinity_regular : OriginalRegularIdealCover318.Property
    (CommRingCat.of (ContactProjectiveQuotientData318.infinityRing R c)) D.infinityIdeal :=
  OriginalRegularSectionIdeal318.property _
    (LineSheafPullback318.line (ContactOriginalRelativePolynomialCharts318.infinityInto R c) L) _
    (ContactResidueSectionRegular318.infinity_regular R c L s hs)
/-- The existing residue-nonzero section is consumed by the arbitrary
projective quotient route with no substituted source, ideal or divisor. -/
lemma regular_charts : OriginalRegularClosedCharts318.Property
    (ContactProjectiveQuotientGluing318.into R c D) :=
  ContactProjectiveQuotientCartier318.regular_charts R c D
    (finite_regular R c L s hs) (infinity_regular R c L s hs)
@[expose] def idealLine : Line (ContactOriginalRelativePolynomialCharts318.curve R c) :=
  ContactProjectiveQuotientCartier318.idealLine R c D
    (finite_regular R c L s hs) (infinity_regular R c L s hs)
/-- Correct relative effective-Cartier scope: closed and regular in the
original source, with flat whole zero family. No degree or Picard
representability is smuggled into this criterion. -/
theorem closed_regular_flat :
    IsClosedImmersion (ContactProjectiveQuotientGluing318.into R c D) ∧
    OriginalRegularClosedCharts318.Property (ContactProjectiveQuotientGluing318.into R c D) ∧
    Flat (ContactProjectiveQuotientGluing318.projection R c D) :=
  ⟨inferInstance,regular_charts R c L s hs,ContactSectionQuotientProperties318.flat R c L s hs⟩
end ContactSectionQuotientCartier318
