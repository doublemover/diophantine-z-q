module
public import OriginalFrameCoverBaseChange318
public import ContactOriginalZeroKernelIso318
public section
noncomputable section
namespace ContactOriginalFrameCover318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalZeroKernelIso318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ)
  (L : Line (curve S c))
abbrev chartScheme (i : Fin 2) : Scheme.{0} := Spec (rings S c i)
lemma image_cover : ⊤≤⨆i,(charts S c i) ''ᵁ ⊤ := by
  simpa only [Scheme.Hom.image_top_eq_opensRange] using ContactOriginalZeroKernelIso318.cover S c
/-- The two ORIGINAL complete finite/infinity charts classify actual
whole global frames by compatible local frames. The overlap equality is
in the SAME ambient module sheaf, including all nonreduced sections. -/
@[expose] def equivalence : OriginalLineFrameUnitTorsor318.Frames L ≃
    {e : OriginalFrameCoverSections318.LocalFrames L (chartScheme S c) (charts S c) //
      OriginalFrameCoverSections318.Compatible L (chartScheme S c) (charts S c) e} :=
  OriginalFrameCoverEquivalence318.equivalence L (chartScheme S c) (charts S c) (image_cover S c)
lemma full_value (e : OriginalLineFrameUnitTorsor318.Frames L) (i : Fin 2) :
    OriginalFrameCoverSections318.pieces L (chartScheme S c) (charts S c)
      ((equivalence S c L) e).val i=
    L.object.presheaf.map (homOfLE (show (charts S c i) ''ᵁ ⊤≤⊤ from le_top)).op
      (e.hom.app ⊤ 1) :=
  OriginalFrameCoverSections318.restrict_value L (chartScheme S c) (charts S c) e i
end ContactOriginalFrameCover318
