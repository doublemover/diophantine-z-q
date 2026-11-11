module
public import ContactHZeroGeometricUnit318
public import ContactGlobalZeroClosed318
public section
noncomputable section
namespace ContactZeroCoefficientCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionZeros318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 OriginalSectionPullbackComposition318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (s : Γ(L.object,⊤))

abbrev pulledSection := pull (curveMap R S f c) L.object s

/-- The actual whole finite zero ideal of the geometrically pulled global
section is the extension of the actual original finite zero ideal. -/
lemma finite_ideal : finiteIdeal S c (L' R S f c L) (pulledSection R S f c L s) =
    Ideal.map (finiteRingMap R S f c).hom (finiteIdeal R c L s) := by
  have hs := congrArg Prod.fst (ContactHZeroGeometricUnit318.geometric_coordinates R c L S f s)
  change finiteSection S c (L' R S f c L) (pulledSection R S f c L s) =
    ContactCoefficientLineCharts318.finiteRestriction R S f c L (finiteSection R c L s) at hs
  change OriginalAffineSectionZero318.ideal _ _ (finiteSection S c _ _) = _
  rw [hs]
  exact OriginalAffineSectionZero318.original_pullback (curveMap R S f c)
    (finiteRingMap R S f c) (finiteInto R c) (finiteInto S c)
    (ContactRelativeCoefficientChange318.finite_square R S f c) L (finiteSection R c L s)
lemma infinity_ideal : infinityIdeal S c (L' R S f c L) (pulledSection R S f c L s) =
    Ideal.map (infinityRingMap R S f c).hom (infinityIdeal R c L s) := by
  have hs := congrArg Prod.snd (ContactHZeroGeometricUnit318.geometric_coordinates R c L S f s)
  change infinitySection S c (L' R S f c L) (pulledSection R S f c L s) =
    ContactCoefficientLineCharts318.infinityRestriction R S f c L (infinitySection R c L s) at hs
  change OriginalAffineSectionZero318.ideal _ _ (infinitySection S c _ _) = _
  rw [hs]
  exact OriginalAffineSectionZero318.original_pullback (curveMap R S f c)
    (infinityRingMap R S f c) (infinityInto R c) (infinityInto S c)
    (ContactRelativeCoefficientChange318.infinity_square R S f c) L (infinitySection R c L s)

@[expose] def finiteMap : finiteZero S c (L' R S f c L) (pulledSection R S f c L s) ⟶ finiteZero R c L s :=
  Spec.map (AffineQuotientPullback318.arrow (finiteRingMap R S f c)
    (finiteIdeal R c L s) (finiteIdeal S c (L' R S f c L) (pulledSection R S f c L s))
    (finite_ideal R S f c L s))
@[expose] def infinityMap : infinityZero S c (L' R S f c L) (pulledSection R S f c L s) ⟶ infinityZero R c L s :=
  Spec.map (AffineQuotientPullback318.arrow (infinityRingMap R S f c)
    (infinityIdeal R c L s) (infinityIdeal S c (L' R S f c L) (pulledSection R S f c L s))
    (infinity_ideal R S f c L s))

lemma finite_pullback : CategoryTheory.IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal S c (L' R S f c L) (pulledSection R S f c L s)))))
    (finiteMap R S f c L s) (Spec.map (finiteRingMap R S f c))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s)))) :=
  AffineQuotientPullback318.pullback_square _ _ _ (finite_ideal R S f c L s)
lemma infinity_pullback : CategoryTheory.IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal S c (L' R S f c L) (pulledSection R S f c L s)))))
    (infinityMap R S f c L s) (Spec.map (infinityRingMap R S f c))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s)))) :=
  AffineQuotientPullback318.pullback_square _ _ _ (infinity_ideal R S f c L s)
end ContactZeroCoefficientCharts318
