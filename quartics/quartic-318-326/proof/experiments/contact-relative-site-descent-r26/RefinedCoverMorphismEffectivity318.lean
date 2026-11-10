module
public import RefinedOriginalLineMapDescent318
public section
noncomputable section
namespace RefinedCoverMorphismEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
abbrev line (D : Datum f) := RefinedCoverObjectEffectivity318.line f g a factor D
abbrev comparison (D : Datum f) := RefinedCoverObjectEffectivity318.comparison f g a factor D

@[expose] def canonicalMap {D E : Datum f} (k : Hom D E) :
    Hom (OriginalCanonicalDescent318.datum f (line f g a factor D))
      (OriginalCanonicalDescent318.datum f (line f g a factor E)) :=
  (RefinedCoverObjectEffectivity318.hom f g a factor D).comp
    (k.comp (RefinedCoverObjectEffectivity318.inverse f g a factor E))

@[expose] def map {D E : Datum f} (k : Hom D E) :
    (line f g a factor D).object ⟶ (line f g a factor E).object :=
  RefinedOriginalLineMapDescent318.descend f g a factor (canonicalMap f g a factor k)

lemma map_cover {D E : Datum f} (k : Hom D E) :
    (Scheme.Modules.pullback f).map (map f g a factor k) ≫ (comparison f g a factor E).hom =
      (comparison f g a factor D).hom ≫ k.sheafHom := by
  rw [show (Scheme.Modules.pullback f).map (map f g a factor k) =
    (canonicalMap f g a factor k).sheafHom from
      RefinedOriginalLineMapDescent318.descend_cover f g a factor (canonicalMap f g a factor k)]
  change (comparison f g a factor D).hom ≫ k.sheafHom ≫ (comparison f g a factor E).inv ≫
    (comparison f g a factor E).hom = _
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

lemma map_unique {D E : Datum f} (k : Hom D E)
    (j : (line f g a factor D).object ⟶ (line f g a factor E).object)
    (hj : (Scheme.Modules.pullback f).map j ≫ (comparison f g a factor E).hom =
      (comparison f g a factor D).hom ≫ k.sheafHom) : j = map f g a factor k := by
  apply RefinedCoverFaithfulness318.pullback_injective f g a factor
  apply (cancel_mono ((comparison f g a factor E).hom)).mp
  exact hj.trans (map_cover f g a factor k).symm

lemma map_id (D : Datum f) : map f g a factor (Hom.id D) = 𝟙 _ := by
  symm
  apply map_unique f g a factor (Hom.id D)
  simp only [Functor.map_id,Category.id_comp,Category.comp_id,Hom.id]

lemma map_comp {D E F : Datum f} (h : Hom D E) (k : Hom E F) :
    map f g a factor (h.comp k) = map f g a factor h ≫ map f g a factor k := by
  symm
  apply map_unique f g a factor (h.comp k)
  rw [Functor.map_comp,Category.assoc,map_cover,← Category.assoc,map_cover,Category.assoc] <;> rfl

/-- Every original compatible map descends uniquely, with its literal
original covering square, not only after restriction to the refinement. -/
theorem effective {D E : Datum f} (k : Hom D E) :
    ∃! j : (line f g a factor D).object ⟶ (line f g a factor E).object,
      (Scheme.Modules.pullback f).map j ≫ (comparison f g a factor E).hom =
        (comparison f g a factor D).hom ≫ k.sheafHom :=
  ⟨map f g a factor k,map_cover f g a factor k,map_unique f g a factor k⟩
end RefinedCoverMorphismEffectivity318
