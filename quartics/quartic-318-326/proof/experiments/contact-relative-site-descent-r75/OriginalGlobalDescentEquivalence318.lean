module
public import OriginalGlobalBaseUnit318
public section
noncomputable section
namespace OriginalGlobalDescentEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalGlobalDescentCategory318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]

/-- The original arbitrary base-line identity join, natural for every
original sheaf map and retaining the exact original reconstructed line. -/
@[expose] def baseComparison : canonical f ⋙ reconstruct f ≅ 𝟭 (Line Y) :=
  NatIso.ofComponents (fun L =>
    { hom := (OriginalGlobalBaseUnit318.iso f L).hom
      inv := (OriginalGlobalBaseUnit318.iso f L).inv
      hom_inv_id := (OriginalGlobalBaseUnit318.iso f L).hom_inv_id
      inv_hom_id := (OriginalGlobalBaseUnit318.iso f L).inv_hom_id }) (by
    intro L K g
    exact OriginalGlobalBaseUnit318.natural f g)

/-- Genuine categorical line descent for an affine faithfully flat
covering morphism over an arbitrary base scheme. Objects and all maps are
original sheaves and original categorical-double descent data; both
natural isomorphisms and the triangle retain the specified actual maps. -/
@[expose] def equivalence : Line Y ≌ OriginalSchemeDescentData318.Datum f where
  functor := canonical f
  inverse := reconstruct f
  unitIso := (baseComparison f).symm
  counitIso := OriginalGlobalDescentCategory318.comparison f
  functor_unitIso_comp L := by
    apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
    change (Scheme.Modules.pullback f).map (OriginalGlobalBaseUnit318.iso f L).inv ≫
      (AffineMorphismGlobalRecovery318.comparison f (OriginalCanonicalDescent318.datum f L)).hom = 𝟙 _
    have hh := congrArg Iso.inv (OriginalGlobalBaseUnit318.iso_cover_iso f L)
    simp only [Functor.mapIso_inv] at hh
    rw [hh]
    exact Iso.inv_hom_id _

/-- The equivalence uses literal original pullback on each sheaf map. -/
lemma functor_map {L K : Line Y} (g : L ⟶ K) :
    ((equivalence f).functor.map g).sheafHom = (Scheme.Modules.pullback f).map g := rfl

/-- The counit component remains exactly the previously constructed
original global covering-line reconstruction, not a replacement witness. -/
lemma counit_component (D : OriginalSchemeDescentData318.Datum f) :
    ((equivalence f).counitIso.hom.app D).sheafHom =
      (AffineMorphismGlobalRecovery318.comparison f D).hom := rfl
end OriginalGlobalDescentEquivalence318
