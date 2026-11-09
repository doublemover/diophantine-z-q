module
public import RefinedCoverMorphismEffectivity318
public section
noncomputable section
namespace RefinedCoverBaseUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  (L : Line Y)
abbrev datum := OriginalCanonicalDescent318.datum f L
abbrev reconstructed := RefinedCoverMorphismEffectivity318.line f g a factor (datum f L)

/-- The refined-cover base unit preserves the same original base line
and is built by actual full original map descent, including its inverse. -/
@[expose] def iso : (reconstructed f g a factor L).object ≅ L.object where
  hom := RefinedOriginalLineMapDescent318.descend f g a factor
    (RefinedCoverObjectEffectivity318.hom f g a factor (datum f L))
  inv := RefinedOriginalLineMapDescent318.descend f g a factor
    (RefinedCoverObjectEffectivity318.inverse f g a factor (datum f L))
  hom_inv_id := by
    apply RefinedCoverFaithfulness318.pullback_injective f g a factor
    rw [Functor.map_comp,RefinedOriginalLineMapDescent318.descend_cover,
      RefinedOriginalLineMapDescent318.descend_cover,CategoryTheory.Functor.map_id]
    exact (RefinedCoverObjectEffectivity318.comparison f g a factor (datum f L)).hom_inv_id
  inv_hom_id := by
    apply RefinedCoverFaithfulness318.pullback_injective f g a factor
    rw [Functor.map_comp,RefinedOriginalLineMapDescent318.descend_cover,
      RefinedOriginalLineMapDescent318.descend_cover,CategoryTheory.Functor.map_id]
    exact (RefinedCoverObjectEffectivity318.comparison f g a factor (datum f L)).inv_hom_id

lemma iso_cover : (Scheme.Modules.pullback f).map (iso f g a factor L).hom =
    (RefinedCoverObjectEffectivity318.comparison f g a factor (datum f L)).hom :=
  RefinedOriginalLineMapDescent318.descend_cover f g a factor
    (RefinedCoverObjectEffectivity318.hom f g a factor (datum f L))
lemma iso_cover_iso : (Scheme.Modules.pullback f).mapIso (iso f g a factor L) =
    RefinedCoverObjectEffectivity318.comparison f g a factor (datum f L) := Iso.ext (iso_cover f g a factor L)

variable {L}
lemma natural {K : Line Y} (h : L.object ⟶ K.object) :
    RefinedCoverMorphismEffectivity318.map f g a factor (OriginalCanonicalDescent318.map f h) ≫
      (iso f g a factor K).hom = (iso f g a factor L).hom ≫ h := by
  apply RefinedCoverFaithfulness318.pullback_injective f g a factor
  rw [Functor.map_comp,Functor.map_comp,iso_cover,iso_cover]
  exact RefinedCoverMorphismEffectivity318.map_cover f g a factor (OriginalCanonicalDescent318.map f h)
end RefinedCoverBaseUnit318
