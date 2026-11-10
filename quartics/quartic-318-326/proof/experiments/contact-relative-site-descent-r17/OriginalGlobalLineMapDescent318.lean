module
public import OriginalGlobalDescentEquivalence318
public section
noncomputable section
namespace OriginalGlobalLineMapDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {L K : Line Y}

/-- Descent of maps between arbitrary original base lines, with no
replacement of either line by a chosen reconstruction. -/
@[expose] def descend (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) : L.object ⟶ K.object :=
  (OriginalGlobalBaseUnit318.iso f L).inv ≫
    AffineGlobalMorphismEffectivity318.map f h ≫ (OriginalGlobalBaseUnit318.iso f K).hom

lemma descend_cover (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) :
    (Scheme.Modules.pullback f).map (descend f h) = h.sheafHom := by
  have hinv := congrArg Iso.inv (OriginalGlobalBaseUnit318.iso_cover_iso f L)
  simp only [Functor.mapIso_inv] at hinv
  simp only [descend,Functor.map_comp,Category.assoc]
  rw [hinv,OriginalGlobalBaseUnit318.iso_cover,AffineGlobalMapCoverSquare318.cover_square,
    Iso.inv_hom_id_assoc]

lemma descend_unique (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) (k : L.object ⟶ K.object)
    (hk : (Scheme.Modules.pullback f).map k = h.sheafHom) : k = descend f h :=
  GlobalAffineLineFaithfulness318.pullback_injective f k (descend f h)
    (hk.trans (descend_cover f h).symm)

@[expose] def homEquiv : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K) ≃ (L.object ⟶ K.object) where
  toFun := descend f
  invFun := OriginalCanonicalDescent318.map f
  left_inv h := Hom.ext (descend_cover f h)
  right_inv k := (descend_unique f (OriginalCanonicalDescent318.map f k) k rfl).symm

/-- The supplied actual covering isomorphism descends, and the covering
map is recovered literally, rather than only up to a scalar. -/
@[expose] def iso (e : (Scheme.Modules.pullback f).obj L.object ≅
    (Scheme.Modules.pullback f).obj K.object)
    (h : Hom (OriginalCanonicalDescent318.datum f L) (OriginalCanonicalDescent318.datum f K))
    (he : h.sheafHom = e.hom) : L.object ≅ K.object where
  hom := descend f h
  inv := descend f (OriginalCanonicalDescent318.inverse f e (by rw [← he]; exact h.commutes))
  hom_inv_id := by
    apply GlobalAffineLineFaithfulness318.pullback_injective f
    rw [Functor.map_comp,descend_cover,descend_cover,CategoryTheory.Functor.map_id,he]
    exact e.hom_inv_id
  inv_hom_id := by
    apply GlobalAffineLineFaithfulness318.pullback_injective f
    rw [Functor.map_comp,descend_cover,descend_cover,CategoryTheory.Functor.map_id,he]
    exact e.inv_hom_id

lemma iso_cover (e : (Scheme.Modules.pullback f).obj L.object ≅
    (Scheme.Modules.pullback f).obj K.object)
    (h : Hom (OriginalCanonicalDescent318.datum f L) (OriginalCanonicalDescent318.datum f K))
    (he : h.sheafHom = e.hom) : (Scheme.Modules.pullback f).mapIso (iso f e h he) = e :=
  Iso.ext ((descend_cover f h).trans he)
end OriginalGlobalLineMapDescent318
