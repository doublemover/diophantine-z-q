module
public import ContactGlobalResidueFlat318
public import ContactZeroGeometricBaseChange318
public section
noncomputable section
namespace ContactZeroParameterBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ)
local notation "q" => ContactRelativeCoefficientChange318.curveMap R S f c
local notation "a" => Spec.map (CommRingCat.ofHom f.toRingHom)

/-- The SAME original coefficient-family map is Cartesian over its
actual coefficient map. Cancel the old p-first pullback from the full
new p-first pullback, retaining both literal projections. -/
lemma ambient_square : IsPullback q (ContactRelativeStructuralHOne318.projection S c)
    (ContactRelativeStructuralHOne318.projection R c) a := by
  apply IsPullback.of_right
    (h₁₂:=pullback.fst (ContactOriginalAffineTestCover318.p c) (baseMap R))
    (h₂₂:=baseMap R)
  · simpa only [RelativeCoefficientChange318.familyMap_original,
      RelativeCoefficientChange318.spec_base] using
      (IsPullback.of_hasPullback (ContactOriginalAffineTestCover318.p c) (baseMap S))
  · exact RelativeCoefficientChange318.familyMap_test (CommRingCat.of ℚ) R S f
      (ContactOriginalAffineTestCover318.p c)
  · exact .of_hasPullback _ _

variable (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- Arbitrary coefficient base change of the actual GLOBAL zero
projection, not merely of its embedding in the ambient curve. -/
lemma square : IsPullback (ContactZeroCoefficientMap318.map R S f c L s)
    (ContactGlobalResidueFlat318.projection S c (L' R S f c L)
      (ContactZeroCoefficientCharts318.pulledSection R S f c L s))
    (ContactGlobalResidueFlat318.projection R c L s) a :=
  (ContactZeroGeometricBaseChange318.square R S f c L s).flip.paste_vert
    (ambient_square R S f c)

/-- The literal coefficient-pulled zero projection is identified with
the canonical pullback projection, with the genuine projection retained. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c (L' R S f c L)
    (ContactZeroCoefficientCharts318.pulledSection R S f c L s) ≅
    pullback (ContactGlobalResidueFlat318.projection R c L s) a :=
  (square R S f c L s).isoPullback
@[reassoc] lemma iso_projection : (iso R S f c L s).hom ≫ pullback.snd _ _ =
    ContactGlobalResidueFlat318.projection S c (L' R S f c L)
      (ContactZeroCoefficientCharts318.pulledSection R S f c L s) :=
  (square R S f c L s).isoPullback_hom_snd
end ContactZeroParameterBaseChange318
