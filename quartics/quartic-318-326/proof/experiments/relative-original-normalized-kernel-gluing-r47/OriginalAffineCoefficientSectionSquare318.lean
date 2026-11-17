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
    eqToIso_refl,NatTrans.id_app,Category.comp_id,Category.id_comp,Category.assoc,
    Functor.comp_obj] <;> rfl

/-- Exact native whole-section form of the original affine restriction.
Both source and target wrappers are explicit, so nested restrictions can
be rewritten before any line-record or native associator normalization. -/
lemma restriction_whole {C D : CommRingCat.{u}} (f : C ⟶ D)
    (L : Line (Spec C)) (N : Line (Spec D))
    (c : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
    (m : OriginalLineAffineModel318.sections C L) :
    OriginalAffinePathWholeSections318.wholeSection N.object
      (OriginalAffineLinePathSections318.restriction f L N c m) =
    c.hom.app ⊤ (OriginalSectionPullbackComposition318.pull (Spec.map f) L.object
      (OriginalAffinePathWholeSections318.wholeSection L.object m)) := by
  have hs := congrArg (OriginalAffinePathWholeSections318.wholeSection N.object)
    (OriginalAffinePathWholeSections318.restriction_direct f L N c m)
  simpa only [OriginalAffinePathWholeSections318.wholeSection,
    OriginalSectionPullbackComposition318.pull,OriginalOpenPullbackSections318.sectionPull] using hs

/-- Project only the underlying original pullback sheaf, without unfolding
the full line record and its geometric frames during normalization. -/
lemma line_object {V W : Scheme.{u}} (f : V ⟶ W) (L : Line W) :
    (LineSheafPullback318.line f L).object = (Scheme.Modules.pullback f).obj L.object := rfl

/-- Typed wrapper for one original coefficient restriction. Keeping the
whole-section map visible prevents a final comparison from reopening the
entire affine scalar-extension carrier. -/
lemma coefficient_restriction_whole {C D : CommRingCat.{u}}
    (f : C ⟶ D) (u : Spec C ⟶ X) (v : Spec D ⟶ Y)
    (hv : Spec.map f ≫ u = v ≫ p) (L : Line X)
    (s : OriginalLineAffineModel318.sections C (LineSheafPullback318.line u L)) :
    OriginalAffinePathWholeSections318.wholeSection
      (LineSheafPullback318.line v (LineSheafPullback318.line p L)).object
      (OriginalCoefficientChartLine318.originalRestriction p f u v hv L s) =
    ((OriginalPullbackSquarePasting318.comparison (Spec.map f) u v p hv).hom.app L.object).app ⊤
      (OriginalSectionPullbackComposition318.pull (Spec.map f)
        ((Scheme.Modules.pullback u).obj L.object)
        (OriginalAffinePathWholeSections318.wholeSection
          (LineSheafPullback318.line u L).object s)) := by
  have hr := restriction_whole f (LineSheafPullback318.line u L)
    (LineSheafPullback318.line v (LineSheafPullback318.line p L))
    (OriginalCoefficientChartLine318.sheafComparison p f u v hv L) s
  simp only [OriginalCoefficientChartLine318.originalRestriction,
    coefficient_comparison,Iso.app_hom] at hr ⊢
  dsimp only [LineSheafPullback318.line,Functor.comp] at hr ⊢
  exact hr

/-- Typed wrapper for one original chart restriction, with the same
whole input section and native path comparison. -/
lemma chart_restriction_whole {Z : Scheme.{u}} {C D : CommRingCat.{u}}
    (f : C ⟶ D) (u : Spec C ⟶ Z) (v : Spec D ⟶ Z)
    (hv : Spec.map f ≫ u = v) (L : Line Z)
    (s : OriginalLineAffineModel318.sections C (LineSheafPullback318.line u L)) :
    OriginalAffinePathWholeSections318.wholeSection (LineSheafPullback318.line v L).object
      (OriginalAffineLinePathSections318.restriction f
        (LineSheafPullback318.line u L) (LineSheafPullback318.line v L)
        ((PullbackPathComposition318.iso (Spec.map f) u v hv).app L.object) s) =
    ((PullbackPathComposition318.iso (Spec.map f) u v hv).hom.app L.object).app ⊤
      (OriginalSectionPullbackComposition318.pull (Spec.map f)
        ((Scheme.Modules.pullback u).obj L.object)
        (OriginalAffinePathWholeSections318.wholeSection
          (LineSheafPullback318.line u L).object s)) := by
  have hr := restriction_whole f (LineSheafPullback318.line u L)
    (LineSheafPullback318.line v L)
    ((PullbackPathComposition318.iso (Spec.map f) u v hv).app L.object) s
  simp only [Iso.app_hom] at hr ⊢
  dsimp only [LineSheafPullback318.line,Functor.comp] at hr ⊢
  exact hr

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
    i' j' (Spec.map e') h' (Spec.map a) (Spec.map b) ha hb he L.object
    (OriginalAffinePathWholeSections318.wholeSection (LineSheafPullback318.line i L).object m)
  conv_lhs => rw [coefficient_restriction_whole,chart_restriction_whole]
  conv_rhs => rw [chart_restriction_whole,coefficient_restriction_whole]
  dsimp only [LineSheafPullback318.line,Functor.comp,Scheme.Opens,
    SheafedSpace.instTopologicalSpaceCarrierCarrier] at hs ⊢
  exact hs
end OriginalAffineCoefficientSectionSquare318
