module
public import AffineOriginalReconstructionSquare318
public section
noncomputable section
namespace AffineOriginalCoverCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOriginalCoverComparison318 AffineOriginalReconstructionSquare318
set_option maxHeartbeats 3400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- Pure-pullback expression for the original covering-line comparison,
using the same calibrated chart map and the same affine reconstruction. -/
@[expose] def comparison (U : Y.affineOpens) :
    (Scheme.Modules.pullback (sourceOpen f U).ι).obj
        ((Scheme.Modules.pullback f).obj (AffineMorphismGlobalLine318.line f D).object) ≅
      (Scheme.Modules.pullback (sourceOpen f U).ι).obj D.line.object :=
  (ActualDescentBaseChangeDiagram318.coverComparison f (f ∣_ U.1) (sourceOpen f U).ι U.1.ι
    (morphismRestrict_ι f U.1).symm).app (AffineMorphismGlobalLine318.line f D).object ≪≫
      (Scheme.Modules.pullback (f ∣_ U.1)).mapIso
        (CalibratedPullbackChartComparison318.comparison f D U) ≪≫ reconstruction f D U

/-- Compatibility holds on every nested pair of original affine base
charts, over the whole original inverse images. Both laws formerly needed
by the generic pasting theorem are now supplied by proved original maps. -/
lemma comparison_nested (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    (Scheme.Modules.pullback (sourceInclusion f U V h)).map (comparison f D U).hom ≫
      (PullbackPathComposition318.iso (sourceInclusion f U V h) (sourceOpen f U).ι
        (sourceOpen f V).ι (Scheme.homOfLE_ι X (f.preimage_mono h))).hom.app D.line.object =
    (PullbackPathComposition318.iso (sourceInclusion f U V h) (sourceOpen f U).ι
      (sourceOpen f V).ι (Scheme.homOfLE_ι X (f.preimage_mono h))).hom.app
        ((Scheme.Modules.pullback f).obj (AffineMorphismGlobalLine318.line f D).object) ≫
          (comparison f D V).hom := by
  have hh := OriginalCoverComparisonPasting318.comparison_pasting
    f (f ∣_ U.1) (f ∣_ V.1) (sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm
    (sourceInclusion f U V h) (Y.homOfLE h) (open_square f U V h)
    (sourceOpen f V).ι V.1.ι (morphismRestrict_ι f V.1).symm
    (Scheme.homOfLE_ι X (f.preimage_mono h)) (Scheme.homOfLE_ι Y h)
    (AffineMorphismGlobalLine318.line f D).object D.line.object
    (OriginalAffineOpenLines318.line f D U.1 U.2).object
    (OriginalAffineOpenLines318.line f D V.1 V.2).object
    (CalibratedPullbackChartComparison318.comparison f D U).hom
    (CalibratedPullbackChartComparison318.comparison f D V).hom
    (OriginalAffineOpenLines318.pullbackComparison f D U.1 V.1 U.2 V.2 h).hom
    (reconstruction f D U).hom (reconstruction f D V).hom
    (CalibratedPullbackChartComparison318.comparison_nested f D U V h)
    (reconstruction_square f D U V h)
  simpa only [comparison,Iso.trans_hom,Iso.app_hom,Functor.mapIso_hom,Category.assoc] using hh
end AffineOriginalCoverCompatibility318
