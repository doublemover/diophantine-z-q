module
public import AffineGlobalMorphismEffectivity318
public section
noncomputable section
namespace OriginalGlobalDescentCategory318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The objects are the unchanged original framed lines; morphisms are
all original module-sheaf maps, not only isomorphisms or chosen scalars. -/
scoped instance lineCategory (X : Scheme.{u}) : Category (Line X) where
  Hom L K := L.object ⟶ K.object
  id L := 𝟙 L.object
  comp g h := g ≫ h
  id_comp := by intros; apply Category.id_comp
  comp_id := by intros; apply Category.comp_id
  assoc := by intros; apply Category.assoc

/-- Descent morphisms retain their actual covering-line map and genuine
double square. No quotient or substitute formal descent object is used. -/
scoped instance datumCategory {X Y : Scheme.{u}} (f : X ⟶ Y) : Category (Datum f) where
  Hom D E := OriginalSchemeDescentBaseChangeMaps318.Hom D E
  id D := OriginalSchemeDescentBaseChangeMaps318.Hom.id D
  comp g h := g.comp h
  id_comp := by intros; apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext; exact Category.id_comp _
  comp_id := by intros; apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext; exact Category.comp_id _
  assoc := by intros; apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext; exact Category.assoc _ _ _

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

@[expose] def canonical : Line Y ⥤ Datum f where
  obj := OriginalCanonicalDescent318.datum f
  map := OriginalCanonicalDescent318.map f
  map_id L := OriginalSchemeDescentBaseChangeMaps318.Hom.ext ((Scheme.Modules.pullback f).map_id L.object)
  map_comp h k := OriginalSchemeDescentBaseChangeMaps318.Hom.ext ((Scheme.Modules.pullback f).map_comp h k)

variable [IsAffineHom f] [Flat f] [Surjective f]

@[expose] def reconstruct : Datum f ⥤ Line Y where
  obj := AffineGlobalMorphismEffectivity318.line f
  map := AffineGlobalMorphismEffectivity318.map f
  map_id := AffineGlobalMorphismEffectivity318.map_id f
  map_comp := AffineGlobalMorphismEffectivity318.map_comp f

/-- The global original comparison is a natural isomorphism of genuine
categories, with the same original covering map as every component. -/
@[expose] def comparison : reconstruct f ⋙ canonical f ≅ 𝟭 (Datum f) :=
  NatIso.ofComponents (fun D =>
    { hom := AffineMorphismGlobalEffectivity318.hom f D
      inv := AffineMorphismGlobalEffectivity318.inverse f D
      hom_inv_id := AffineMorphismGlobalEffectivity318.hom_inverse f D
      inv_hom_id := AffineMorphismGlobalEffectivity318.inverse_hom f D }) (by
    intro D E k
    apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
    exact AffineGlobalMapCoverSquare318.cover_square f k)

end OriginalGlobalDescentCategory318
