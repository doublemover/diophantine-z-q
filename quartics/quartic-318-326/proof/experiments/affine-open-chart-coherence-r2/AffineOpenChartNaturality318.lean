module
public import OriginalAffineOpenLines318
public section
noncomputable section
namespace AffineOpenChartNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineFaithfullyFlatChart318 AffineOpenChartRefinement318 AffineOpenChartComparison318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
local instance sourceAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := algebra f U
local instance targetAlgebra : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := algebra f V
local instance sourceFF : Module.FaithfullyFlat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  module_faithfullyFlat f U hU
local instance targetFF : Module.FaithfullyFlat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
  module_faithfullyFlat f V hV
variable {D E : OriginalSchemeDescentData318.Datum f}
  (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E)

/-- The exact nested-chart reconstruction comparison is natural for every
original covering-line map compatible with the original geometric overlap. -/
lemma comparison_natural :
    (Scheme.Modules.pullback (baseMap U V h)).map
        (ActualAffineDescendedMaps318.map (AffineOpenChartDescent318.mapDatum f U hU k)) ≫
      (comparison f U V hU hV h E).hom =
    (comparison f U V hU hV h D).hom ≫
      ActualAffineDescendedMaps318.map (AffineOpenChartDescent318.mapDatum f V hV k) := by
  let m := ActualAffineDescendedMaps318.map (AffineOpenChartDescent318.mapDatum f U hU k)
  let P := Scheme.Modules.pullback (map f V)
  have hn := (ActualDescentBaseChangeDiagram318.coverComparison (map f U) (map f V)
    (sourceMap f U V h) (baseMap U V h) (square f U V hU hV h)).inv.naturality m
  change P.map ((Scheme.Modules.pullback (baseMap U V h)).map m) ≫
      (squarePath f U V hU hV h E).inv =
    (squarePath f U V hU hV h D).inv ≫
      (Scheme.Modules.pullback (sourceMap f U V h)).map
        ((Scheme.Modules.pullback (map f U)).map m) at hn
  have hp := (PullbackPathComposition318.iso (sourceMap f U V h)
    (source f U hU) (source f V hV) (source_fromSpec f U V hU hV h)).hom.naturality k.sheafHom
  change (Scheme.Modules.pullback (sourceMap f U V h)).map
      ((Scheme.Modules.pullback (source f U hU)).map k.sheafHom) ≫
        (coveringPath f U V hU hV h E).hom =
    (coveringPath f U V hU hV h D).hom ≫
      (Scheme.Modules.pullback (source f V hV)).map k.sheafHom at hp
  apply OriginalAffineLineFaithfulness318.maps_eq_of_cover_square Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
    _ _ (AffineOpenChartDescent318.comparison f V hV E)
  simp only [Functor.map_comp, Category.assoc]
  rw [comparison_cover, ActualAffineDescendedMaps318.map_commutes]
  rw [← Category.assoc (P.map (comparison f U V hU hV h D).hom), comparison_cover]
  rw [← Category.assoc (P.map ((Scheme.Modules.pullback (baseMap U V h)).map m)), hn,
    Category.assoc, ← Functor.map_comp_assoc, ActualAffineDescendedMaps318.map_commutes,
    Functor.map_comp]
  change (squarePath f U V hU hV h D).inv ≫
      ((Scheme.Modules.pullback (sourceMap f U V h)).map
        (AffineOpenChartDescent318.comparison f U hU D).hom ≫
          (Scheme.Modules.pullback (sourceMap f U V h)).map
            ((Scheme.Modules.pullback (source f U hU)).map k.sheafHom)) ≫
              (coveringPath f U V hU hV h E).hom = _
  simp only [Category.assoc]
  rw [hp]
end AffineOpenChartNaturality318
