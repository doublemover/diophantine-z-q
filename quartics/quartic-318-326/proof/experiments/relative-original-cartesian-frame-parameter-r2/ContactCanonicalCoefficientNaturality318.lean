module
public import ContactCanonicalCoefficientFrame318
public section
noncomputable section
namespace ContactCanonicalCoefficientNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318 ContactCanonicalCoefficientFrame318
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
lemma base_comp : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ base R S f=base R T (g.comp f) := by
  rw [←Spec.map_comp]
  rfl
abbrev coefficient : family R T (g.comp f) c ⟶ family R S f c :=
  RelativeSchemeCoefficient318.map (projection R c) (base R S f) (base R T (g.comp f))
    (Spec.map (CommRingCat.ofHom g.toRingHom)) (base_comp R S T f g)
lemma model_square : (model R T (g.comp f) c).hom ≫ coefficient R S T f g c=
    ContactRelativeCoefficientChange318.curveMap S T g c ≫ (model R S f c).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc,RelativeSchemeCoefficient318.map_fst,
      (cartesian R T (g.comp f) c).isoPullback_hom_fst,
      Category.assoc,(cartesian R S f c).isoPullback_hom_fst]
    exact (ContactCoefficientWholeOpens318.composition R S f c T g).symm
  · rw [Category.assoc,RelativeSchemeCoefficient318.map_snd,←Category.assoc,
      (cartesian R T (g.comp f) c).isoPullback_hom_snd,
      Category.assoc,(cartesian R S f c).isoPullback_hom_snd]
    exact (RelativeCoefficientChange318.familyMap_test (CommRingCat.of ℚ) S T g
      (ContactIntrinsicDifferentials318.structureMap c)).symm
/-- The actual Cartesian-model frame equivalence is natural under every
original coefficient map, retaining native path comparisons on BOTH sides. -/
lemma natural (a : Frames (line R S f c L)) :
    equivalence R T (g.comp f) c L
      (OriginalFramePathTransport318.transport L (coefficient R S T f g c)
        (pullback.fst (projection R c) (base R S f))
        (pullback.fst (projection R c) (base R T (g.comp f)))
        (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) a)=
    OriginalFramePathTransport318.transport L (ContactRelativeCoefficientChange318.curveMap S T g c)
      (original R S f c) (original R T (g.comp f) c)
      (ContactCoefficientWholeOpens318.composition R S f c T g)
      (equivalence R S f c L a) :=
  OriginalFrameModelNaturality318.natural L (model R S f c).hom (model R T (g.comp f) c).hom
    (ContactRelativeCoefficientChange318.curveMap S T g c) (coefficient R S T f g c)
    (original R S f c) (pullback.fst (projection R c) (base R S f))
    (original R T (g.comp f) c) (pullback.fst (projection R c) (base R T (g.comp f)))
    (cartesian R S f c).isoPullback_hom_fst (cartesian R T (g.comp f) c).isoPullback_hom_fst
    (ContactCoefficientWholeOpens318.composition R S f c T g)
    (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) (model_square R S T f g c) a
end ContactCanonicalCoefficientNaturality318
