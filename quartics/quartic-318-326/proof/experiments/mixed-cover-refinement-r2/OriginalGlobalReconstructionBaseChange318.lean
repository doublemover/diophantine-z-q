module
public import OriginalGlobalSquareFunctor318
public section
noncomputable section
namespace OriginalGlobalReconstructionBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
  [IsAffineHom f] [Flat f] [Surjective f] [IsAffineHom g] [Flat g] [Surjective g]
  (a : X' ⟶ X) (b : Y' ⟶ Y) (square : a ≫ f = g ≫ b) (D : Datum f)
abbrev changed := OriginalSchemeDescentBaseChange318.datum f g a b square D
variable {f} in
abbrev originalLine := AffineGlobalMorphismEffectivity318.line f D
variable {f} in
abbrev pulledLine := LineSheafPullback318.line b (originalLine D)
abbrev changedLine := AffineGlobalMorphismEffectivity318.line g (changed f g a b square D)
abbrev coverPath := (ActualDescentBaseChangeDiagram318.coverComparison f g a b square).app (originalLine D).object
abbrev changedComparison := AffineMorphismGlobalRecovery318.comparison g (changed f g a b square D)

/-- The canonical comparison inverse and the original reconstructed
comparison after a-pullback give an actual morphism to the changed datum. -/
@[expose] def toChanged : Hom (OriginalCanonicalDescent318.datum g (pulledLine b D))
    (changed f g a b square D) :=
  (OriginalCanonicalDescent318.baseChangeInverse f g a b square (originalLine D)).comp
    (OriginalSchemeDescentBaseChangeMaps318.map g a b square (AffineMorphismGlobalEffectivity318.hom f D))

@[expose] def coveringIso : (Scheme.Modules.pullback g).obj (pulledLine b D).object ≅
    (Scheme.Modules.pullback g).obj (changedLine f g a b square D).object :=
  (coverPath f g a b square D).symm ≪≫
    (Scheme.Modules.pullback a).mapIso (AffineMorphismGlobalRecovery318.comparison f D) ≪≫
      (changedComparison f g a b square D).symm

@[expose] def coveringHom : Hom (OriginalCanonicalDescent318.datum g (pulledLine b D))
    (OriginalCanonicalDescent318.datum g (changedLine f g a b square D)) :=
  (toChanged f g a b square D).comp
    (AffineMorphismGlobalEffectivity318.inverse g (changed f g a b square D))

/-- Reconstruction commutes with every actual commuting square between
affine faithfully flat covers, over arbitrary base schemes. -/
@[expose] def comparison : (pulledLine b D).object ≅ (changedLine f g a b square D).object :=
  OriginalGlobalLineMapDescent318.iso g (coveringIso f g a b square D)
    (coveringHom f g a b square D) rfl

lemma comparison_cover :
    (Scheme.Modules.pullback g).map (comparison f g a b square D).hom ≫
      (changedComparison f g a b square D).hom =
    (coverPath f g a b square D).inv ≫
      (Scheme.Modules.pullback a).map (AffineMorphismGlobalRecovery318.comparison f D).hom := by
  have h := congrArg Iso.hom (OriginalGlobalLineMapDescent318.iso_cover g
    (coveringIso f g a b square D) (coveringHom f g a b square D) rfl)
  simp only [Functor.mapIso_hom] at h
  change (Scheme.Modules.pullback g).map (comparison f g a b square D).hom =
    (coveringIso f g a b square D).hom at h
  rw [h]
  simp only [coveringIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]

lemma comparison_unique (k : (pulledLine b D).object ⟶ (changedLine f g a b square D).object)
    (hk : (Scheme.Modules.pullback g).map k ≫ (changedComparison f g a b square D).hom =
      (coverPath f g a b square D).inv ≫
        (Scheme.Modules.pullback a).map (AffineMorphismGlobalRecovery318.comparison f D).hom) :
    k = (comparison f g a b square D).hom := by
  apply GlobalAffineLineFaithfulness318.pullback_injective g
  apply (cancel_mono (changedComparison f g a b square D).hom).mp
  exact hk.trans (comparison_cover f g a b square D).symm
end OriginalGlobalReconstructionBaseChange318
