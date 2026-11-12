module
public import ContactResidueRegularFlat318
public import OriginalAffineFiberwiseRegular318
public import ContactFieldIntegralLine318
public import ContactRelativeCoefficientChange318
public section
noncomputable section
namespace ContactResidueSectionRegular318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

local notation "ResidueNonzero" => ContactResidueRegularFlat318.ResidueNonzero R c L s

/-- The complete ORIGINAL finite-chart SECTION is intrinsically regular over the full base, using
the proven geometrically integral contact model in each residue field. -/
lemma finite_regular (hs : ResidueNonzero) :
    SectionZeroRegularCoordinate318.Regular (R ⊗[ℚ] finiteRing c)
      (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] finiteRing c))
        (LineSheafPullback318.line (finiteInto R c) L)) (pull (finiteInto R c) L.object s) := by
  apply OriginalAffineFiberwiseRegular318.regular
  intro m hm
  letI := hm
  exact OriginalIntegralCoefficientSection318.injective (CommRingCat.of ℚ) R
    (CommRingCat.of (R⧸m)) (finiteRing c) (Ideal.Quotient.mkₐ ℚ m)
    (ContactOriginalAffineTestCover318.p c) (SourceGlobalAffine318.chartEmbedding c)
    (finite_over c) L s (hs m hm)

/-- Intrinsic regularity on the complete reciprocal chart; its actual original
ring and actual infinity restriction are retained, not replaced by t. -/
lemma infinity_regular (hs : ResidueNonzero) :
    SectionZeroRegularCoordinate318.Regular (R ⊗[ℚ] infinityRing c)
      (OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[ℚ] infinityRing c))
        (LineSheafPullback318.line (infinityInto R c) L)) (pull (infinityInto R c) L.object s) := by
  apply OriginalAffineFiberwiseRegular318.regular
  intro m hm
  letI := hm
  exact OriginalIntegralCoefficientSection318.injective (CommRingCat.of ℚ) R
    (CommRingCat.of (R⧸m)) (infinityRing c) (Ideal.Quotient.mkₐ ℚ m)
    (ContactOriginalAffineTestCover318.p c) (ContactWholeInfinityScheme318.into c)
    (infinity_over c) L s (hs m hm)
end ContactResidueSectionRegular318
