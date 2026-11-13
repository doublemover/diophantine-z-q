module
public import RefinementDescentFaithfulness318
public section
noncomputable section
namespace RefinementCanonicalComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalGlobalDescentCategory318 OriginalGlobalSquareFunctor318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  (a : U ⟶ X) (factor : a ≫ f = g)
abbrev change : OriginalSchemeDescentData318.Datum f ⥤ OriginalSchemeDescentData318.Datum g :=
  OriginalGlobalSquareFunctor318.change f g a (𝟙 Y) (by rw [factor,Category.comp_id])

/-- The exact canonical square comparison followed by the original
identity-pullback unit, natural in every original base-line map. -/
@[expose] def comparison : canonical f ⋙ change f g a factor ≅ canonical g :=
  NatIso.ofComponents (fun L =>
    { hom := (OriginalCanonicalDescent318.baseChange f g a (𝟙 Y)
        (by rw [factor,Category.comp_id]) L).comp
        (OriginalCanonicalDescent318.map g ((Scheme.Modules.pullbackId Y).hom.app L.object))
      inv := (OriginalCanonicalDescent318.map g ((Scheme.Modules.pullbackId Y).inv.app L.object)).comp
        (OriginalCanonicalDescent318.baseChangeInverse f g a (𝟙 Y)
          (by rw [factor,Category.comp_id]) L)
      hom_inv_id := by
        apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
        simp only [OriginalSchemeDescentBaseChangeMaps318.Hom.comp,
          OriginalCanonicalDescent318.baseChange,OriginalCanonicalDescent318.baseChangeInverse,
          OriginalCanonicalDescent318.inverse,OriginalCanonicalDescent318.map,Iso.app_hom,Iso.app_inv,Category.assoc,
          ← Functor.map_comp_assoc,Iso.hom_inv_id_app,Functor.map_id,Category.id_comp,
          Iso.hom_inv_id_app]
      inv_hom_id := by
        apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
        simp only [OriginalSchemeDescentBaseChangeMaps318.Hom.comp,
          OriginalCanonicalDescent318.baseChange,OriginalCanonicalDescent318.baseChangeInverse,
          OriginalCanonicalDescent318.inverse,OriginalCanonicalDescent318.map,Iso.app_hom,Iso.app_inv,Category.assoc,
          Iso.inv_hom_id_app_assoc,← Functor.map_comp,Iso.inv_hom_id_app,Functor.map_id] }) (by
    intro L K h
    apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
    let C := ActualDescentBaseChangeDiagram318.coverComparison f g a (𝟙 Y)
      (by rw [factor,Category.comp_id])
    change (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f).map h) ≫
        C.hom.app K.object ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app K.object) =
      C.hom.app L.object ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app L.object) ≫
        (Scheme.Modules.pullback g).map h
    rw [← Category.assoc,C.hom.naturality h,Category.assoc,← Functor.map_comp]
    rw [(Scheme.Modules.pullbackId Y).hom.naturality h,Functor.map_comp]
    simp only [Category.assoc])
end RefinementCanonicalComparison318
