module
public import OriginalIntegralCoefficientSection318
public import OriginalAffineRegularFiberFlat318
public import ContactFieldIntegralLine318
public import ContactRelativeCoefficientChange318
public section
noncomputable section
namespace ContactResidueRegularFlat318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- Actual nonzero geometric residue sections, before choosing either
original chart. No coordinate injectivity or dual pairing is assumed. -/
def ResidueNonzero : Prop := ∀ m : Ideal R, ∀ _ : m.IsMaximal,
  pull (ContactRelativeCoefficientChange318.curveMap R (CommRingCat.of (R⧸m))
    (Ideal.Quotient.mkₐ ℚ m) c) L.object s≠0

/-- The complete ORIGINAL finite-chart zero projection is flat, using
the proven geometrically integral contact model in each residue field. -/
lemma finite_flat (hs : ResidueNonzero R c L s) :
    Flat (OriginalAffineSectionFlat318.projection R (finiteRing c)
      (LineSheafPullback318.line (finiteInto R c) L) (pull (finiteInto R c) L.object s)) := by
  apply OriginalAffineRegularFiberFlat318.projection_flat
  intro m hm
  letI := hm
  exact OriginalIntegralCoefficientSection318.injective (CommRingCat.of ℚ) R
    (CommRingCat.of (R⧸m)) (finiteRing c) (Ideal.Quotient.mkₐ ℚ m)
    (ContactOriginalAffineTestCover318.p c) (SourceGlobalAffine318.chartEmbedding c)
    (finite_over c) L s (hs m hm)

/-- The SAME result on the complete reciprocal chart; its actual original
ring and actual infinity restriction are retained, not replaced by t. -/
lemma infinity_flat (hs : ResidueNonzero R c L s) :
    Flat (OriginalAffineSectionFlat318.projection R (infinityRing c)
      (LineSheafPullback318.line (infinityInto R c) L) (pull (infinityInto R c) L.object s)) := by
  apply OriginalAffineRegularFiberFlat318.projection_flat
  intro m hm
  letI := hm
  exact OriginalIntegralCoefficientSection318.injective (CommRingCat.of ℚ) R
    (CommRingCat.of (R⧸m)) (infinityRing c) (Ideal.Quotient.mkₐ ℚ m)
    (ContactOriginalAffineTestCover318.p c) (ContactWholeInfinityScheme318.into c)
    (infinity_over c) L s (hs m hm)
end ContactResidueRegularFlat318
