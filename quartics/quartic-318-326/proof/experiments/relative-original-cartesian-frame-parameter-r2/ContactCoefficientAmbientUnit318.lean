module
public import OriginalWholeOpenCoefficientSquare318
public import ContactOriginalDerivedCoefficientMap318
public section
noncomputable section
namespace ContactCoefficientAmbientUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionTransport318 OriginalOpenPullbackSections318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318 ContactRelativeWholeOpenSections318
open ContactRelativeCoefficientChange318 ContactCoefficientWholeOpens318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))

lemma image_preimage : curveMap R S f c ⁻¹ᵁ (into R c ''ᵁ ⊤) = into S c ''ᵁ ⊤ := by
  simp only [overlap_image,Scheme.Hom.preimage_inf,finite_preimage,infinity_preimage]

/-- The previously missing original affine/ambient unit square is proved
on EVERY actual Laurent section, including all original transports. -/
lemma square (s : originalSections R c L) :
    overlapEquiv S c (ContactCoefficientLineCharts318.pulledLine R S f c L)
      (ContactCoefficientLineCharts318.overlapRestriction R S f c L s) =
    ContactOriginalDerivedCoefficientMap318.overlapPull R S f c L (overlapEquiv R c L s) := by
  have hh : sectionsEquiv (into S c)
      (ContactCoefficientLineCharts318.pulledLine R S f c L).object
      (ContactCoefficientLineCharts318.overlapRestriction R S f c L s) =
    pullTo (curveMap R S f c) L.object (into R c ''ᵁ ⊤) (into S c ''ᵁ ⊤)
      (image_preimage R S f c) (sectionsEquiv (into R c) L.object s) := by
    change sectionsEquiv (into S c) _ (OriginalAffineLinePathSections318.restriction
      (overlapRingMap R S f c) _ _ _ s) = _
    rw [OriginalAffinePathWholeSections318.restriction_direct]
    exact OriginalWholeOpenCoefficientSquare318.square (curveMap R S f c)
      (into R c) (into S c) (Spec.map (overlapRingMap R S f c))
      (overlap_square R S f c) (image_preimage R S f c) L.object s
  change move _ (overlap_image S c)
    (sectionsEquiv (into S c) _ (ContactCoefficientLineCharts318.overlapRestriction R S f c L s)) = _
  rw [hh]
  exact change_opens (curveMap R S f c) L.object (into R c ''ᵁ ⊤)
    (finiteOpen R c ⊓ infinityOpen R c) (into S c ''ᵁ ⊤)
    (finiteOpen S c ⊓ infinityOpen S c) (image_preimage R S f c)
    (overlap_preimage R S f c) (overlap_image R c) (overlap_image S c)
    (sectionsEquiv (into R c) L.object s)
end ContactCoefficientAmbientUnit318
