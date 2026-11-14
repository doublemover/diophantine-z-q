module
public import CanonicalCoverPastingInverse318
public section
noncomputable section
namespace AffineOpenChartComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineFaithfullyFlatChart318 AffineOpenChartRefinement318 AffineOpenChartComparison318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (U V W : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
  (h : V ≤ U) (k : W ≤ V) (D : OriginalSchemeDescentData318.Datum f)
local instance targetAlgebra : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := algebra f W
local instance targetFF : Module.FaithfullyFlat Γ(Y, W) Γ(X, f ⁻¹ᵁ W) :=
  module_faithfullyFlat f W hW

abbrev basePath := (PullbackPathComposition318.iso (baseMap V W k) (baseMap U V h)
  (baseMap U W (k.trans h)) (base_composition U V h W k)).app
    (AffineOpenChartDescent318.line f U hU D).object

/-- The actual reconstructed transitions satisfy the original nested
chart cocycle, with the named original base pullback-composition map.
Only the original global descent datum is an input. -/
lemma composition :
    (Scheme.Modules.pullback (baseMap V W k)).map (comparison f U V hU hV h D).hom ≫
      (comparison f V W hV hW k D).hom =
    (basePath f U V W hU h k D).hom ≫
      (comparison f U W hU hW (k.trans h) D).hom := by
  let P := Scheme.Modules.pullback (map f W)
  let M := (AffineOpenChartDescent318.line f U hU D).object
  let a₁ := sourceMap f U V h
  let a₂ := sourceMap f V W k
  let a₃ := sourceMap f U W (k.trans h)
  let b₁ := baseMap U V h
  let b₂ := baseMap V W k
  let b₃ := baseMap U W (k.trans h)
  let A := PullbackPathComposition318.iso a₂ a₁ a₃ (source_composition f U V h W k)
  let C := ActualDescentBaseChangeDiagram318.coverComparison (map f V) (map f W)
    a₂ b₂ (square f V W hV hW k)
  have hn := C.inv.naturality (comparison f U V hU hV h D).hom
  change P.map ((Scheme.Modules.pullback b₂).map (comparison f U V hU hV h D).hom) ≫
      (squarePath f V W hV hW k D).inv =
    C.inv.app ((Scheme.Modules.pullback b₁).obj M) ≫
      (Scheme.Modules.pullback a₂).map
        ((Scheme.Modules.pullback (map f V)).map (comparison f U V hU hV h D).hom) at hn
  have ha := A.hom.naturality (AffineOpenChartDescent318.comparison f U hU D).hom
  have hs := PullbackPathComposition318.assoc a₂ a₁ (source f U hU)
    a₃ (source f V hV) (source f W hW)
    (source_composition f U V h W k) (source_fromSpec f U V hU hV h)
    (source_fromSpec f U W hU hW (k.trans h)) (source_fromSpec f V W hV hW k) D.line.object
  have hc := CanonicalCoverPastingInverse318.cover_pasting (map f U) (map f V) (map f W)
    a₁ b₁ (square f U V hU hV h) a₂ b₂ (square f V W hV hW k)
    a₃ b₃ (square f U W hU hW (k.trans h))
    (source_composition f U V h W k) (base_composition U V h W k) M
  apply OriginalAffineLineFaithfulness318.maps_eq_of_cover_square Γ(Y, W) Γ(X, f ⁻¹ᵁ W)
    _ _ (AffineOpenChartDescent318.comparison f W hW D)
  simp only [Functor.map_comp, Category.assoc]
  rw [comparison_cover, comparison_cover]
  rw [← Category.assoc (P.map ((Scheme.Modules.pullback b₂).map
    (comparison f U V hU hV h D).hom)), hn, Category.assoc]
  rw [← Functor.map_comp_assoc, comparison_cover, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hs]
  rw [← Category.assoc ((Scheme.Modules.pullback a₂).map
    ((Scheme.Modules.pullback a₁).map (AffineOpenChartDescent318.comparison f U hU D).hom)), ha]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ (Scheme.Modules.pullback a₃).map
      (AffineOpenChartDescent318.comparison f U hU D).hom ≫
        (coveringPath f U W hU hW (k.trans h) D).hom) hc
end AffineOpenChartComposition318
