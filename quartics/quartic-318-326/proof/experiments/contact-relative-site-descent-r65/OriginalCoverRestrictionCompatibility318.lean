module
public import PullbackRestrictionCompatibility318
public section
noncomputable section
namespace OriginalCoverRestrictionCompatibility318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- Converting the pure comparison to restrictions gives literally the
previously displayed original full-inverse-image comparison. -/
lemma comparison_eq (U : Y.affineOpens) :
    PullbackRestrictionCompatibility318.restriction
      (AffineOriginalCoverCompatibility318.comparison f D U) =
        AffineOriginalCoverComparison318.comparison f D U := by
  apply Iso.ext
  simp only [PullbackRestrictionCompatibility318.restriction,
    AffineOriginalCoverCompatibility318.comparison,
    AffineOriginalCoverComparison318.comparison,AffineOriginalCoverComparison318.openPath,
    CalibratedPullbackChartComparison318.comparison,
    AffineOriginalReconstructionSquare318.reconstruction,PullbackChartNaturality318.chartNatIso,
    ActualDescentBaseChangeDiagram318.coverComparison,PullbackPathComposition318.iso,
    Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,Iso.app_hom,Iso.app_inv,NatTrans.comp_app,
    Functor.mapIso_hom,Functor.map_comp,Functor.isoWhiskerLeft,
    Functor.isoWhiskerRight,Functor.whiskerLeft_app,Functor.whiskerRight_app,
    Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,Iso.refl_inv,
    NatTrans.id_app,Functor.map_id,Category.comp_id,Category.id_comp,Category.assoc]

/-- The unchanged original source-chart isomorphisms agree under actual
restriction on every nested original affine base chart. -/
lemma comparison_nested (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    OpenSheafRestrictionCompatibility318.schemeRestrict
      (AffineOriginalCoverComparison318.comparison f D U) (f.preimage_mono h) =
        AffineOriginalCoverComparison318.comparison f D V := by
  rw [← comparison_eq f D U,← comparison_eq f D V]
  exact PullbackRestrictionCompatibility318.compatible (f.preimage_mono h)
    (AffineOriginalCoverCompatibility318.comparison f D U)
    (AffineOriginalCoverCompatibility318.comparison f D V)
    (AffineOriginalCoverCompatibility318.comparison_nested f D U V h)
end OriginalCoverRestrictionCompatibility318
