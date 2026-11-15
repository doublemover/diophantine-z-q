module
public import OriginalCoefficientChartLine318
public import OriginalLineSquareSections318
public import OriginalAffinePathWholeSections318
public section
noncomputable section
namespace OriginalAffineCoefficientSectionSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} {A B A' B' : CommRingCat.{u}}
  (p : Y ⟶ X) (i : Spec A ⟶ X) (j : Spec B ⟶ X) (e : A ⟶ B)
  (h : Spec.map e ≫ i = j)
  (i' : Spec A' ⟶ Y) (j' : Spec B' ⟶ Y) (e' : A' ⟶ B')
  (h' : Spec.map e' ≫ i' = j') (a : A ⟶ A') (b : B ⟶ B')
  (ha : Spec.map a ≫ i = i' ≫ p) (hb : Spec.map b ≫ j = j' ≫ p)
  (he : Spec.map b ≫ Spec.map e = Spec.map e' ≫ Spec.map a)

/-- Normalize the coefficient comparison on abstract scheme/ring carriers,
not after substituting concrete tensor-pushout chart implementations. -/
lemma coefficient_comparison (L : Line X) :
    OriginalCoefficientChartLine318.sheafComparison p b j j' hb L =
      (OriginalPullbackSquarePasting318.comparison (Spec.map b) j j' p hb).app L.object := by
  apply Iso.ext
  simp only [OriginalCoefficientChartLine318.sheafComparison,
    OriginalPullbackSquarePasting318.comparison,PullbackPathComposition318.iso,
    Iso.trans_hom,Iso.symm_hom,Iso.trans_inv,Iso.refl_hom,Iso.refl_inv,
    NatTrans.comp_app,Iso.app_hom,Iso.app_inv,Scheme.Modules.pullbackCongr,
    eqToIso_refl,NatTrans.id_app,Category.comp_id,Category.id_comp,Category.assoc]

include he in
/-- The original affine restrictions commute on every section. All native
associator/unit normalization is checked while chart carriers stay abstract;
concrete consumers need only unfold their own wrapper names. -/
lemma original_square (L : Line X)
    (m : OriginalLineAffineModel318.sections A (LineSheafPullback318.line i L)) :
    OriginalCoefficientChartLine318.originalRestriction p b j j' hb L
      (OriginalAffineLinePathSections318.restriction e
        (LineSheafPullback318.line i L) (LineSheafPullback318.line j L)
        ((PullbackPathComposition318.iso (Spec.map e) i j h).app L.object) m) =
    OriginalAffineLinePathSections318.restriction e'
      (LineSheafPullback318.line i' (LineSheafPullback318.line p L))
      (LineSheafPullback318.line j' (LineSheafPullback318.line p L))
      ((PullbackPathComposition318.iso (Spec.map e') i' j' h').app
        (LineSheafPullback318.line p L).object)
      (OriginalCoefficientChartLine318.originalRestriction p a i i' ha L m) := by
  apply OriginalAffinePathWholeSections318.wholeSection_injective
    (LineSheafPullback318.line j' (LineSheafPullback318.line p L)).object
  have hs := OriginalLineSquareSections318.original_square p i j (Spec.map e) h
    i' j' (Spec.map e') h' (Spec.map a) (Spec.map b) ha hb he L.object m
  simpa only [OriginalCoefficientChartLine318.originalRestriction,
    OriginalAffinePathWholeSections318.restriction_direct,
    coefficient_comparison,Iso.app_hom,OriginalLineAffineModel318.sections,
    LineSheafPullback318.line,OriginalAffinePathWholeSections318.wholeSection,
    Functor.comp_obj,OriginalOpenPullbackSections318.sectionPull,
    OriginalSectionPullbackComposition318.pull] using hs
end OriginalAffineCoefficientSectionSquare318
