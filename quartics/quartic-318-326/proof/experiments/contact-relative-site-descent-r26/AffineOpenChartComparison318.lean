module
public import AffineOpenChartRefinement318
public import OriginalDescentBaseChangePath318
public section
noncomputable section
namespace AffineOpenChartComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AffineFaithfullyFlatChart318 AffineOpenChartRefinement318
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
local instance sourceAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := algebra f U
local instance targetAlgebra : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := algebra f V
variable (D : OriginalSchemeDescentData318.Datum f)

abbrev changed := AffineChangedBaseEffectivity318.datum Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
  Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (sourceMap f U V h) (baseMap U V h) (square f U V hU hV h)
  (AffineOpenChartDescent318.datum f U hU D)
abbrev coveringPath := (PullbackPathComposition318.iso (sourceMap f U V h)
  (source f U hU) (source f V hV) (source_fromSpec f U V hU hV h)).app D.line.object

/-- The actual successive/direct chart path intertwines the original
changed overlap with the original smaller-chart overlap. -/
@[expose] def datumHom : ActualAffineDescentData318.Hom (changed f U V hU hV h D)
    (AffineOpenChartDescent318.datum f V hV D) where
  sheafHom := (coveringPath f U V hU hV h D).hom
  commutes := (OriginalDescentBaseChangePath318.hom f (map f U) (map f V)
    (source f U hU) (base U hU) (AffineFaithfullyFlatChart318.square f U hU)
    (sourceMap f U V h) (baseMap U V h) (square f U V hU hV h)
    (source f V hV) (base V hV) (AffineFaithfullyFlatChart318.square f V hV)
    (source_fromSpec f U V hU hV h) (base_fromSpec U V hU hV h) D).commutes

@[expose] def datumInv : ActualAffineDescentData318.Hom
    (AffineOpenChartDescent318.datum f V hV D) (changed f U V hU hV h D) where
  sheafHom := (coveringPath f U V hU hV h D).inv
  commutes := (OriginalDescentBaseChangePath318.inv f (map f U) (map f V)
    (source f U hU) (base U hU) (AffineFaithfullyFlatChart318.square f U hU)
    (sourceMap f U V h) (baseMap U V h) (square f U V hU hV h)
    (source f V hV) (base V hV) (AffineFaithfullyFlatChart318.square f V hV)
    (source_fromSpec f U V hU hV h) (base_fromSpec U V hU hV h) D).commutes

variable [Flat f] [Surjective f]
local instance sourceFF : Module.FaithfullyFlat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  module_faithfullyFlat f U hU
local instance targetFF : Module.FaithfullyFlat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
  module_faithfullyFlat f V hV

abbrev changedIso := ActualAffineDescendedMaps318.iso (datumHom f U V hU hV h D)
  (datumInv f U V hU hV h D) (coveringPath f U V hU hV h D).hom_inv_id
    (coveringPath f U V hU hV h D).inv_hom_id
abbrev baseComparison := AffineReconstructionBaseChange318.comparison
  Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  (sourceMap f U V h) (baseMap U V h) (square f U V hU hV h)
  (AffineOpenChartDescent318.datum f U hU D)

/-- Literal restriction of the reconstructed original chart line is
isomorphic to the reconstructed line on the smaller original affine chart. -/
@[expose] def comparison :
    (Scheme.Modules.pullback (baseMap U V h)).obj (AffineOpenChartDescent318.line f U hU D).object ≅
      (AffineOpenChartDescent318.line f V hV D).object :=
  baseComparison f U V hU hV h D ≪≫ changedIso f U V hU hV h D

abbrev squarePath := (ActualDescentBaseChangeDiagram318.coverComparison (map f U) (map f V)
  (sourceMap f U V h) (baseMap U V h) (square f U V hU hV h)).app
    (AffineOpenChartDescent318.line f U hU D).object

/-- The transition uses both original chart reconstruction maps and the
actual pullback path all the way back to the original global covering line. -/
lemma comparison_cover :
    (Scheme.Modules.pullback (map f V)).map (comparison f U V hU hV h D).hom ≫
        (AffineOpenChartDescent318.comparison f V hV D).hom =
      (squarePath f U V hU hV h D).inv ≫
        (Scheme.Modules.pullback (sourceMap f U V h)).map
          (AffineOpenChartDescent318.comparison f U hU D).hom ≫
            (coveringPath f U V hU hV h D).hom := by
  change (Scheme.Modules.pullback (map f V)).map
      ((baseComparison f U V hU hV h D).hom ≫ (changedIso f U V hU hV h D).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc,
    ActualAffineDescendedMaps318.map_commutes (datumHom f U V hU hV h D), ← Category.assoc,
    AffineReconstructionBaseChange318.comparison_cover]
  simp only [Category.assoc]

lemma comparison_unique
    (k : (Scheme.Modules.pullback (baseMap U V h)).obj (AffineOpenChartDescent318.line f U hU D).object ⟶
      (AffineOpenChartDescent318.line f V hV D).object)
    (hk : (Scheme.Modules.pullback (map f V)).map k ≫
        (AffineOpenChartDescent318.comparison f V hV D).hom =
      (squarePath f U V hU hV h D).inv ≫
        (Scheme.Modules.pullback (sourceMap f U V h)).map
          (AffineOpenChartDescent318.comparison f U hU D).hom ≫
            (coveringPath f U V hU hV h D).hom) : k = (comparison f U V hU hV h D).hom := by
  apply OriginalAffineLineFaithfulness318.maps_eq_of_cover_square Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
    k (comparison f U V hU hV h D).hom (AffineOpenChartDescent318.comparison f V hV D)
  exact hk.trans (comparison_cover f U V hU hV h D).symm

end AffineOpenChartComparison318
