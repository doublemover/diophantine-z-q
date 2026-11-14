module
public import AffineBasisModuleIsomorphisms318
public import LocalLineCategoricalDescent318
public section
noncomputable section
namespace AffineChartAmbientComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OpenChartModuleImages318 OpenSheafRestrictionCompatibility318 OpenRestrictionPathCoherence318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

abbrev opens : Y.affineOpens → Y.Opens := fun U => U.1
abbrev localLine (U : Y.affineOpens) := OriginalAffineOpenLines318.line f D U.1 U.2
abbrev modules (U : Y.affineOpens) := (localLine f D U).object
abbrev ambient (U : Y.affineOpens) := OpenChartModuleImages318.ambient (opens (Y:=Y)) (modules f D) U

/-- On every original affine subchart, the actual direct image of the
original local reconstruction recovers that subchart's own reconstruction. -/
@[expose] def comparison (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    (ambient f D U).restrict V.1.ι ≅ (localLine f D V).object :=
  subchartRecovery (opens (Y:=Y)) (modules f D) U V.1 h ≪≫
    OriginalAffineOpenLines318.restrictionComparison f D U.1 V.1 U.2 V.2 h

/-- This exact ambient comparison respects original affine subchart
restriction; the original direct-image counit and collapse are retained. -/
lemma comparison_restrict (U V W : Y.affineOpens) (h : V.1 ≤ U.1) (k : W.1 ≤ V.1) :
    path (ambient f D U) k ≪≫
      (Scheme.Modules.restrictFunctor (Y.homOfLE k)).mapIso (comparison f D U V h) ≪≫
        OriginalAffineOpenLines318.restrictionComparison f D V.1 W.1 V.2 W.2 k =
      comparison f D U W (k.trans h) := by
  have hc := OriginalOpenRestrictionComposition318.composition f D U.1 V.1 W.1 U.2 V.2 W.2 h k
  have hs := congrArg Iso.hom
    (subchartRecovery_comp (opens (Y:=Y)) (modules f D) U k h)
  apply Iso.ext
  simp only [comparison, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hc]
  have hs' : (path (ambient f D U) k).hom ≫
      (Scheme.Modules.restrictFunctor (Y.homOfLE k)).map
        (subchartRecovery (opens (Y:=Y)) (modules f D) U V.1 h).hom ≫
      (RestrictionTransitionPasting318.collapse (Y.homOfLE k) (Y.homOfLE h)
        (Y.homOfLE (k.trans h)) (OriginalOpenPullbackComposition318.inclusion_comp k h)).hom.app
        (modules f D U) =
    (subchartRecovery (opens (Y:=Y)) (modules f D) U W.1 (k.trans h)).hom := by
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
      collapse, RestrictionTransitionPasting318.collapse] using hs
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (OriginalAffineOpenLines318.restrictionComparison f D U.1 W.1 U.2 W.2 (k.trans h)).hom) hs'
end AffineChartAmbientComparison318
