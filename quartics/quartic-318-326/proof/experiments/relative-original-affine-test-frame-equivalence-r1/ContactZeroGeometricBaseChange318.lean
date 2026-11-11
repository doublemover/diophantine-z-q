module
public import ContactZeroCoefficientMap318
public section
noncomputable section
namespace ContactZeroGeometricBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactCoefficientNativeSections318 ContactRelativeCoefficientChange318
open ContactGlobalSectionZero318 ContactZeroCoefficientCharts318
open ContactGlobalZeroChartSquares318 ContactGlobalZeroClosed318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- The original zero-scheme construction commutes with ARBITRARY
coefficient base change as an actual geometric Cartesian square. The
section is the genuine geometric pullback of the original global section;
no flatness, reducedness or matching-point surrogate is assumed. -/
lemma square : IsPullback
    (ContactGlobalSectionZero318.into S c (L' R S f c L) (pulledSection R S f c L s))
    (ContactZeroCoefficientMap318.map R S f c L s) (curveMap R S f c)
    (ContactGlobalSectionZero318.into R c L s) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (originalCover S c)
  intro i
  fin_cases i
  · let hs := (ContactGlobalZeroChartSquares318.finite_square S c (L' R S f c L) (pulledSection R S f c L s)).flip
    have hp := (finite_pullback R S f c L s).paste_vert (ContactGlobalZeroChartSquares318.finite_square R c L s)
    change IsPullback (pullback.snd
      (ContactGlobalSectionZero318.into S c (L' R S f c L) (pulledSection R S f c L s)) (finiteInto S c))
      (pullback.fst _ _ ≫ ContactZeroCoefficientMap318.map R S f c L s)
      (finiteInto S c ≫ curveMap R S f c) (ContactGlobalSectionZero318.into R c L s)
    apply hp.of_iso hs.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom,Category.comp_id,hs.isoPullback_hom_snd]
    · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,hs.isoPullback_hom_fst,
        ContactZeroCoefficientMap318.finiteChart_map]
    · simpa only [Iso.refl_hom,Category.comp_id,Category.id_comp] using
        ContactRelativeCoefficientChange318.finite_square R S f c
    · simp
  · let hs := (ContactGlobalZeroChartSquares318.infinity_square S c (L' R S f c L) (pulledSection R S f c L s)).flip
    have hp := (infinity_pullback R S f c L s).paste_vert (ContactGlobalZeroChartSquares318.infinity_square R c L s)
    change IsPullback (pullback.snd
      (ContactGlobalSectionZero318.into S c (L' R S f c L) (pulledSection R S f c L s)) (infinityInto S c))
      (pullback.fst _ _ ≫ ContactZeroCoefficientMap318.map R S f c L s)
      (infinityInto S c ≫ curveMap R S f c) (ContactGlobalSectionZero318.into R c L s)
    apply hp.of_iso hs.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom,Category.comp_id,hs.isoPullback_hom_snd]
    · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,hs.isoPullback_hom_fst,
        ContactZeroCoefficientMap318.infinityChart_map]
    · simpa only [Iso.refl_hom,Category.comp_id,Category.id_comp] using
        ContactRelativeCoefficientChange318.infinity_square R S f c
    · simp

@[expose] def baseChangeIso : scheme S c (L' R S f c L) (pulledSection R S f c L s) ≅
    pullback (curveMap R S f c) (ContactGlobalSectionZero318.into R c L s) :=
  (square R S f c L s).isoPullback
@[simp,reassoc] lemma baseChangeIso_fst : (baseChangeIso R S f c L s).hom ≫ pullback.fst _ _ =
    ContactGlobalSectionZero318.into S c (L' R S f c L) (pulledSection R S f c L s) :=
  (square R S f c L s).isoPullback_hom_fst
@[simp,reassoc] lemma baseChangeIso_snd : (baseChangeIso R S f c L s).hom ≫ pullback.snd _ _ =
    ContactZeroCoefficientMap318.map R S f c L s :=
  (square R S f c L s).isoPullback_hom_snd
end ContactZeroGeometricBaseChange318
