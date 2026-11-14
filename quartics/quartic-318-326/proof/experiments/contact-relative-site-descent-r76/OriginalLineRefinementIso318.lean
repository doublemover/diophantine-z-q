module
public import ContactRelativeCechDescent318
public section
noncomputable section
namespace OriginalLineRefinementIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ActualAffineBaseRefinement318.Refinement f)
  {L K : Line Y}

/-- Descend the supplied original covering isomorphism through the actual
specified affine refinement, with the original f-cover recovery unchanged. -/
@[expose] def iso (e : (Scheme.Modules.pullback f).obj L.object ≅
    (Scheme.Modules.pullback f).obj K.object)
    (h : Hom (OriginalCanonicalDescent318.datum f L) (OriginalCanonicalDescent318.datum f K))
    (he : h.sheafHom = e.hom) : L.object ≅ K.object where
  hom := RefinedOriginalLineMapDescent318.descend f r.map r.lift r.factor h
  inv := RefinedOriginalLineMapDescent318.descend f r.map r.lift r.factor
    (OriginalCanonicalDescent318.inverse f e (by rw [← he]; exact h.commutes))
  hom_inv_id := by
    apply RefinedCoverFaithfulness318.pullback_injective f r.map r.lift r.factor
    rw [Functor.map_comp,RefinedOriginalLineMapDescent318.descend_cover,
      RefinedOriginalLineMapDescent318.descend_cover,CategoryTheory.Functor.map_id,he]
    exact e.hom_inv_id
  inv_hom_id := by
    apply RefinedCoverFaithfulness318.pullback_injective f r.map r.lift r.factor
    rw [Functor.map_comp,RefinedOriginalLineMapDescent318.descend_cover,
      RefinedOriginalLineMapDescent318.descend_cover,CategoryTheory.Functor.map_id,he]
    exact e.inv_hom_id

lemma iso_cover (e : (Scheme.Modules.pullback f).obj L.object ≅
    (Scheme.Modules.pullback f).obj K.object)
    (h : Hom (OriginalCanonicalDescent318.datum f L) (OriginalCanonicalDescent318.datum f K))
    (he : h.sheafHom = e.hom) : (Scheme.Modules.pullback f).mapIso (iso f r e h he) = e :=
  Iso.ext ((RefinedOriginalLineMapDescent318.descend_cover f r.map r.lift r.factor h).trans he)
end OriginalLineRefinementIso318
