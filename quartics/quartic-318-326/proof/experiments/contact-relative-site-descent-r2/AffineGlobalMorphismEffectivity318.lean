module
public import AffineGlobalMapCoverSquare318
public section
noncomputable section
namespace AffineGlobalMorphismEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
abbrev line (D : Datum f) := AffineMorphismGlobalLine318.line f D
abbrev comparison (D : Datum f) := AffineMorphismGlobalRecovery318.comparison f D
abbrev map {D E : Datum f} (k : Hom D E) := AffineGlobalDescendedMap318.map f k

lemma map_unique {D E : Datum f} (k : Hom D E)
    (g : (line f D).object ⟶ (line f E).object)
    (hg : (Scheme.Modules.pullback f).map g ≫ (comparison f E).hom =
      (comparison f D).hom ≫ k.sheafHom) : g = map f k := by
  apply GlobalAffineLineFaithfulness318.pullback_injective f
  apply (cancel_mono (comparison f E).hom).mp
  exact hg.trans (AffineGlobalMapCoverSquare318.cover_square f k).symm

/-- Every original compatible covering-line map descends uniquely to a
map between the unchanged globally reconstructed base lines. -/
theorem effective {D E : Datum f} (k : Hom D E) :
    ∃! g : (line f D).object ⟶ (line f E).object,
      (Scheme.Modules.pullback f).map g ≫ (comparison f E).hom =
        (comparison f D).hom ≫ k.sheafHom :=
  ⟨map f k,AffineGlobalMapCoverSquare318.cover_square f k,map_unique f k⟩

lemma map_id (D : Datum f) : map f (Hom.id D) = 𝟙 (line f D).object := by
  apply GlobalAffineLineFaithfulness318.pullback_injective f
  apply (cancel_mono (comparison f D).hom).mp
  simpa only [Hom.id,Functor.map_id,Category.id_comp,Category.comp_id] using
    AffineGlobalMapCoverSquare318.cover_square f (Hom.id D)

lemma map_comp {D E F : Datum f} (h : Hom D E) (k : Hom E F) :
    map f (h.comp k) = map f h ≫ map f k := by
  apply GlobalAffineLineFaithfulness318.pullback_injective f
  apply (cancel_mono (comparison f F).hom).mp
  rw [Functor.map_comp,Category.assoc,AffineGlobalMapCoverSquare318.cover_square,
    ← Category.assoc,AffineGlobalMapCoverSquare318.cover_square,Category.assoc]
  exact AffineGlobalMapCoverSquare318.cover_square f (h.comp k)

/-- Original compatible isomorphisms descend with exactly their supplied
inverse equations, checked after the original faithfully flat pullback. -/
@[expose] def iso {D E : Datum f} (h : Hom D E) (k : Hom E D)
    (hk : h.sheafHom ≫ k.sheafHom = 𝟙 _) (kh : k.sheafHom ≫ h.sheafHom = 𝟙 _) :
    (line f D).object ≅ (line f E).object where
  hom := map f h
  inv := map f k
  hom_inv_id := by
    rw [← map_comp,show h.comp k = Hom.id D from Hom.ext hk,map_id]
  inv_hom_id := by
    rw [← map_comp,show k.comp h = Hom.id E from Hom.ext kh,map_id]

lemma map_cocycle {D E F : Datum f} (h : Hom D E) (k : Hom E F) (j : Hom D F)
    (hj : h.sheafHom ≫ k.sheafHom = j.sheafHom) : map f h ≫ map f k = map f j := by
  rw [← map_comp,show h.comp k = j from Hom.ext hj]
end AffineGlobalMorphismEffectivity318
