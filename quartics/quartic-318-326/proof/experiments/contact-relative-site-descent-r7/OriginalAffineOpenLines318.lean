module
public import AffineOpenChartComparison318
public section
noncomputable section
namespace OriginalAffineOpenLines318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineFaithfullyFlatChart318 AffineOpenChartRefinement318
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- The reconstructed line is returned to the original open subscheme,
with its genuine local frames transported by original sheaf pullback. -/
abbrev line (U : Y.Opens) (hU : IsAffineOpen U) : Line U.toScheme :=
  LineSheafPullback318.line hU.isoSpec.hom (AffineOpenChartDescent318.line f U hU D)

variable (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)

lemma chart_square : Y.homOfLE h ≫ hU.isoSpec.hom =
    hV.isoSpec.hom ≫ baseMap U V h :=
  (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map V U h).symm

/-- Both comparisons use the same original homOfLE and affine chart maps. -/
abbrev path := (PullbackPathComposition318.iso (Y.homOfLE h) hU.isoSpec.hom
    (hV.isoSpec.hom ≫ baseMap U V h) (chart_square U V hU hV h)).app
      (AffineOpenChartDescent318.line f U hU D).object ≪≫
  ((PullbackPathComposition318.iso hV.isoSpec.hom (baseMap U V h)
    (hV.isoSpec.hom ≫ baseMap U V h) rfl).app
      (AffineOpenChartDescent318.line f U hU D).object).symm

/-- Actual pullback restriction on the original open schemes, not merely
an isomorphism class on their spectra. -/
@[expose] def pullbackComparison :
    (Scheme.Modules.pullback (Y.homOfLE h)).obj (line f D U hU).object ≅
      (line f D V hV).object :=
  path f D U V hU hV h ≪≫
    (Scheme.Modules.pullback hV.isoSpec.hom).mapIso
      (AffineOpenChartComparison318.comparison f U V hU hV h D)

/-- The very restriction functor consumed by Fi-only open gluing, using
the original restriction/pullback comparison rather than a new action. -/
@[expose] def restrictionComparison :
    (line f D U hU).object.restrict (Y.homOfLE h) ≅ (line f D V hV).object :=
  (Scheme.Modules.restrictFunctorIsoPullback (Y.homOfLE h)).app (line f D U hU).object ≪≫
    pullbackComparison f D U V hU hV h

lemma restrictionComparison_hom : (restrictionComparison f D U V hU hV h).hom =
    (Scheme.Modules.restrictFunctorIsoPullback (Y.homOfLE h)).hom.app (line f D U hU).object ≫
      (path f D U V hU hV h).hom ≫
        (Scheme.Modules.pullback hV.isoSpec.hom).map
          (AffineOpenChartComparison318.comparison f U V hU hV h D).hom := by
  simp only [restrictionComparison, pullbackComparison, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
end OriginalAffineOpenLines318
