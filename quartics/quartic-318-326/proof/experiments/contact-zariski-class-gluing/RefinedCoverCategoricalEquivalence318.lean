module
public import RefinedCoverBaseUnit318
public section
noncomputable section
namespace RefinedCoverCategoricalEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalSchemeDescentData318
open OriginalGlobalDescentCategory318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)

@[expose] def reconstruct : Datum f ⥤ Line Y where
  obj := RefinedCoverMorphismEffectivity318.line f g a factor
  map := RefinedCoverMorphismEffectivity318.map f g a factor
  map_id := RefinedCoverMorphismEffectivity318.map_id f g a factor
  map_comp := RefinedCoverMorphismEffectivity318.map_comp f g a factor

@[expose] def coverComparison : reconstruct f g a factor ⋙ canonical f ≅ 𝟭 (Datum f) :=
  NatIso.ofComponents (fun D =>
    { hom := RefinedCoverObjectEffectivity318.hom f g a factor D
      inv := RefinedCoverObjectEffectivity318.inverse f g a factor D
      hom_inv_id := RefinedCoverObjectEffectivity318.hom_inverse f g a factor D
      inv_hom_id := RefinedCoverObjectEffectivity318.inverse_hom f g a factor D }) (by
    intro D E h
    apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
    exact RefinedCoverMorphismEffectivity318.map_cover f g a factor h)

@[expose] def baseComparison : canonical f ⋙ reconstruct f g a factor ≅ 𝟭 (Line Y) :=
  NatIso.ofComponents (fun L =>
    { hom := (RefinedCoverBaseUnit318.iso f g a factor L).hom
      inv := (RefinedCoverBaseUnit318.iso f g a factor L).inv
      hom_inv_id := (RefinedCoverBaseUnit318.iso f g a factor L).hom_inv_id
      inv_hom_id := (RefinedCoverBaseUnit318.iso f g a factor L).inv_hom_id }) (by
    intro L K h
    exact RefinedCoverBaseUnit318.natural f g a factor h)

/-- Original line/descent category equivalence for every original arrow
with the displayed affine faithfully flat refinement. The forward functor
is literal original pullback; all objects, maps, units and counits retain
the original sheaves and genuine original double equations. -/
@[expose] def equivalence : Line Y ≌ Datum f where
  functor := canonical f
  inverse := reconstruct f g a factor
  unitIso := (baseComparison f g a factor).symm
  counitIso := coverComparison f g a factor
  functor_unitIso_comp L := by
    apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
    change (Scheme.Modules.pullback f).map (RefinedCoverBaseUnit318.iso f g a factor L).inv ≫
      (RefinedCoverObjectEffectivity318.comparison f g a factor (OriginalCanonicalDescent318.datum f L)).hom = 𝟙 _
    have he := congrArg Iso.inv (RefinedCoverBaseUnit318.iso_cover_iso f g a factor L)
    simp only [Functor.mapIso_inv] at he
    rw [he]
    exact Iso.inv_hom_id _
end RefinedCoverCategoricalEquivalence318
