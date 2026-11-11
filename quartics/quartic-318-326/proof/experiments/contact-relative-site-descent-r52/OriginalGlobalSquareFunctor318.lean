module
public import OriginalGlobalLineMapDescent318
public section
noncomputable section
namespace OriginalGlobalSquareFunctor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalGlobalDescentCategory318 OriginalSchemeDescentData318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
  (a : X' ⟶ X) (b : Y' ⟶ Y) (square : a ≫ f = g ≫ b)

@[expose] def linePullback : Line Y ⥤ Line Y' where
  obj := LineSheafPullback318.line b
  map := (Scheme.Modules.pullback b).map
  map_id L := (Scheme.Modules.pullback b).map_id L.object
  map_comp h k := (Scheme.Modules.pullback b).map_comp h k

/-- Actual descent data and all original compatible maps change along
any commuting square; the square need not be cartesian. -/
@[expose] def change : Datum f ⥤ Datum g where
  obj := OriginalSchemeDescentBaseChange318.datum f g a b square
  map := OriginalSchemeDescentBaseChangeMaps318.map g a b square
  map_id := OriginalSchemeDescentBaseChangeMaps318.map_id g a b square
  map_comp := OriginalSchemeDescentBaseChangeMaps318.map_comp g a b square

/-- The original covering-square comparison is natural in the original
base line and is an isomorphism of actual descent data. -/
@[expose] def canonicalComparison : canonical f ⋙ change f g a b square ≅
    linePullback b ⋙ canonical g :=
  NatIso.ofComponents (fun L =>
    { hom := OriginalCanonicalDescent318.baseChange f g a b square L
      inv := OriginalCanonicalDescent318.baseChangeInverse f g a b square L
      hom_inv_id := by
        apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
        exact ((ActualDescentBaseChangeDiagram318.coverComparison f g a b square).app L.object).hom_inv_id
      inv_hom_id := by
        apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
        exact ((ActualDescentBaseChangeDiagram318.coverComparison f g a b square).app L.object).inv_hom_id }) (by
    intro L K h
    apply OriginalSchemeDescentBaseChangeMaps318.Hom.ext
    exact (ActualDescentBaseChangeDiagram318.coverComparison f g a b square).hom.naturality h)
end OriginalGlobalSquareFunctor318
