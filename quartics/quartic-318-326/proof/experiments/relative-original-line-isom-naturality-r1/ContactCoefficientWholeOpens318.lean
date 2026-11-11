module
public import ContactRelativeCoefficientChange318
public import ContactRelativeWholeOpenSections318
public import RelativeCoefficientFunctor318
public section
namespace ContactCoefficientWholeOpens318
open AlgebraicGeometry CategoryTheory
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactRelativeCoefficientChange318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ)

/-- Exact inverse-image equality of the whole original finite open,
not just an inclusion deduced from a commuting affine square. -/
lemma finite_preimage : curveMap R S f c ⁻¹ᵁ finiteOpen R c = finiteOpen S c := by
  simp only [finiteOpen,Scheme.Hom.image_top_eq_opensRange,finite_range]
  change curveMap R S f c ⁻¹ᵁ
    (_ ⁻¹ᵁ ContactOriginalAffineTestCover318.finiteOpen c) = _
  rw [← Scheme.Hom.comp_preimage,RelativeCoefficientChange318.familyMap_original]

/-- The distinct reciprocal chart is pulled back in its entirety too. -/
lemma infinity_preimage : curveMap R S f c ⁻¹ᵁ infinityOpen R c = infinityOpen S c := by
  simp only [infinityOpen,Scheme.Hom.image_top_eq_opensRange,infinity_range]
  change curveMap R S f c ⁻¹ᵁ
    (_ ⁻¹ᵁ ContactOriginalAffineTestCover318.infinityOpen c) = _
  rw [← Scheme.Hom.comp_preimage,RelativeCoefficientChange318.familyMap_original]

lemma overlap_preimage : curveMap R S f c ⁻¹ᵁ
    (finiteOpen R c ⊓ infinityOpen R c) = finiteOpen S c ⊓ infinityOpen S c := by
  rw [Scheme.Hom.preimage_inf,finite_preimage,infinity_preimage]

lemma identity : curveMap R R (AlgHom.id ℚ R) c = 𝟙 _ :=
  RelativeCoefficientFunctor318.family_identity (CommRingCat.of ℚ) R
    (ContactOriginalAffineTestCover318.p c)

variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : S →ₐ[ℚ] T)
lemma composition : curveMap S T g c ≫ curveMap R S f c = curveMap R T (g.comp f) c :=
  RelativeCoefficientFunctor318.family_composition _ _ _ _ _ _ _
end ContactCoefficientWholeOpens318
