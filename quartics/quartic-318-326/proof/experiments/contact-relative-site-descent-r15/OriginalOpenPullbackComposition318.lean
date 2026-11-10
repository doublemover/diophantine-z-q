module
public import SheafComparisonPasting318
public section
noncomputable section
namespace OriginalOpenPullbackComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOpenChartRefinement318 OriginalAffineOpenLines318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y : Scheme.{u}} {U V W : Y.Opens}

lemma inclusion_comp (h : W ≤ V) (k : V ≤ U) :
    Y.homOfLE h ≫ Y.homOfLE k = Y.homOfLE (h.trans k) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

variable {X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)
  (U V W : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
  (h : V ≤ U) (k : W ≤ V)

/-- The original open-subscheme pullback comparisons satisfy their exact
nested-chart cocycle. This transports the proved spectrum reconstruction
cocycle; no new open-subscheme transition law is an assumption. -/
lemma composition :
    (Scheme.Modules.pullback (Y.homOfLE k)).map (pullbackComparison f D U V hU hV h).hom ≫
      (pullbackComparison f D V W hV hW k).hom =
    (PullbackPathComposition318.iso (Y.homOfLE k) (Y.homOfLE h)
      (Y.homOfLE (k.trans h)) (inclusion_comp k h)).hom.app (line f D U hU).object ≫
        (pullbackComparison f D U W hU hW (k.trans h)).hom := by
  have hh := SheafComparisonPasting318.transition_pasting hU.isoSpec.hom hV.isoSpec.hom hW.isoSpec.hom
    (Y.homOfLE h) (baseMap U V h) (chart_square U V hU hV h)
    (Y.homOfLE k) (baseMap V W k) (chart_square V W hV hW k)
    (Y.homOfLE (k.trans h)) (baseMap U W (k.trans h)) (chart_square U W hU hW (k.trans h))
    (inclusion_comp k h) (base_composition U V h W k)
    (AffineOpenChartComparison318.comparison f U V hU hV h D).hom
    (AffineOpenChartComparison318.comparison f V W hV hW k D).hom
    (AffineOpenChartComparison318.comparison f U W hU hW (k.trans h) D).hom
    (AffineOpenChartComposition318.composition f U V W hU hV hW h k D)
  simpa only [pullbackComparison, path, ActualDescentBaseChangeDiagram318.coverComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    Functor.mapIso_hom, Category.assoc] using hh
end OriginalOpenPullbackComposition318
