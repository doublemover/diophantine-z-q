module
public import OriginalReconstructionTransport318
public section
noncomputable section
namespace AffineOriginalReconstructionSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOriginalCoverComparison318 AffineOpenChartRefinement318
set_option maxHeartbeats 3400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- The unchanged actual affine reconstruction, returned to the whole
original inverse-image open and the original covering-line pullback. -/
@[expose] def reconstruction (U : Y.affineOpens) :
    (Scheme.Modules.pullback (f ∣_ U.1)).obj (OriginalAffineOpenLines318.line f D U.1 U.2).object ≅
      (Scheme.Modules.pullback (sourceOpen f U).ι).obj D.line.object :=
  affinePath f D U ≪≫
    (Scheme.Modules.pullback (sourceAffine f U).isoSpec.hom).mapIso
      (AffineOpenChartDescent318.comparison f U.1 U.2 D) ≪≫ sourcePath f D U

variable (U V : Y.affineOpens) (h : V.1 ≤ U.1)
abbrev sourceInclusion : (sourceOpen f V).toScheme ⟶ (sourceOpen f U).toScheme :=
  X.homOfLE (f.preimage_mono h)

lemma source_chart_square : sourceInclusion f U V h ≫ (sourceAffine f U).isoSpec.hom =
    (sourceAffine f V).isoSpec.hom ≫ sourceMap f U.1 V.1 h :=
  (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map (sourceOpen f V) (sourceOpen f U)
    (f.preimage_mono h)).symm

lemma open_square : sourceInclusion f U V h ≫ (f ∣_ U.1) =
    (f ∣_ V.1) ≫ Y.homOfLE h :=
  (morphismRestrict_homOfLE f V.1 U.1 h).symm

/-- The missing original-open reconstruction law is now derived from the
actual spectrum reconstruction equation. No local compatibility, chart
cocycle or normalization premise is added. -/
lemma reconstruction_square :
    (Scheme.Modules.pullback (f ∣_ V.1)).map
      (OriginalAffineOpenLines318.pullbackComparison f D U.1 V.1 U.2 V.2 h).hom ≫
        (reconstruction f D V).hom =
    (ActualDescentBaseChangeDiagram318.coverComparison (f ∣_ U.1) (f ∣_ V.1)
      (sourceInclusion f U V h) (Y.homOfLE h) (open_square f U V h)).inv.app
        (OriginalAffineOpenLines318.line f D U.1 U.2).object ≫
      (Scheme.Modules.pullback (sourceInclusion f U V h)).map (reconstruction f D U).hom ≫
        (PullbackPathComposition318.iso (sourceInclusion f U V h) (sourceOpen f U).ι
          (sourceOpen f V).ι (Scheme.homOfLE_ι X (f.preimage_mono h))).hom.app D.line.object := by
  have hh := OriginalReconstructionTransport318.reconstruction_square
    (AffineFaithfullyFlatChart318.map f U.1) (AffineFaithfullyFlatChart318.map f V.1)
    (f ∣_ U.1) (f ∣_ V.1)
    (sourceAffine f U).isoSpec.hom U.2.isoSpec.hom (chart_square f U).symm
    (sourceAffine f V).isoSpec.hom V.2.isoSpec.hom (chart_square f V).symm
    (sourceMap f U.1 V.1 h) (baseMap U.1 V.1 h) (square f U.1 V.1 U.2 V.2 h)
    (sourceInclusion f U V h) (Y.homOfLE h) (open_square f U V h)
    (source_chart_square f U V h) (OriginalAffineOpenLines318.chart_square U.1 V.1 U.2 V.2 h)
    (sourceAffine f U).fromSpec (sourceAffine f V).fromSpec (source_fromSpec f U.1 V.1 U.2 V.2 h)
    (sourceOpen f U).ι (sourceOpen f V).ι
    (sourceAffine f U).isoSpec_hom_fromSpec (sourceAffine f V).isoSpec_hom_fromSpec
    (Scheme.homOfLE_ι X (f.preimage_mono h)) D.line.object
    (AffineOpenChartDescent318.line f U.1 U.2 D).object
    (AffineOpenChartDescent318.line f V.1 V.2 D).object
    (AffineOpenChartComparison318.comparison f U.1 V.1 U.2 V.2 h D).hom
    (AffineOpenChartDescent318.comparison f U.1 U.2 D).hom
    (AffineOpenChartDescent318.comparison f V.1 V.2 D).hom
    (AffineOpenChartComparison318.comparison_cover f U.1 V.1 U.2 V.2 h D)
  simp only [reconstruction,affinePath,Iso.trans_hom,Iso.app_hom,Functor.mapIso_hom,
    PullbackSquareTarget318.cover_flip] at ⊢
  simpa only [OriginalAffineOpenLines318.pullbackComparison,OriginalAffineOpenLines318.path,
    ActualDescentBaseChangeDiagram318.coverComparison,sourcePath,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,NatTrans.comp_app,Functor.mapIso_hom,Category.assoc] using hh
end AffineOriginalReconstructionSquare318
