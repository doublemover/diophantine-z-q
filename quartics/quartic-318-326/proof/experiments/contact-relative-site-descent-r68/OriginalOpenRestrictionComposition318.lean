module
public import RestrictionTransitionPasting318
public section
noncomputable section
namespace OriginalOpenRestrictionComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalAffineOpenLines318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)
  (U V W : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
  (h : V ≤ U) (k : W ≤ V)

/-- The actual Fi-only restriction comparisons satisfy the precise
original nested-chart cocycle required for subsequent open gluing. -/
lemma composition :
    (Scheme.Modules.restrictFunctor (Y.homOfLE k)).map
        (restrictionComparison f D U V hU hV h).hom ≫
      (restrictionComparison f D V W hV hW k).hom =
    (RestrictionTransitionPasting318.collapse (Y.homOfLE k) (Y.homOfLE h)
      (Y.homOfLE (k.trans h)) (OriginalOpenPullbackComposition318.inclusion_comp k h)).hom.app
        (line f D U hU).object ≫
      (restrictionComparison f D U W hU hW (k.trans h)).hom := by
  have hh := RestrictionTransitionPasting318.transition_pasting
    (Y.homOfLE k) (Y.homOfLE h) (Y.homOfLE (k.trans h))
    (OriginalOpenPullbackComposition318.inclusion_comp k h)
    (pullbackComparison f D U V hU hV h).hom
    (pullbackComparison f D V W hV hW k).hom
    (pullbackComparison f D U W hU hW (k.trans h)).hom
    (OriginalOpenPullbackComposition318.composition f D U V W hU hV hW h k)
  simpa only [restrictionComparison, Iso.trans_hom, Iso.app_hom, Category.assoc] using hh
end OriginalOpenRestrictionComposition318
