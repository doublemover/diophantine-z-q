module
public import OriginalCanonicalDescent318
public section
noncomputable section
namespace OriginalLocalRecoveryDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
open AffineOriginalCoverComparison318
set_option maxHeartbeats 3400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : Datum f) (U : Y.affineOpens)

abbrev restrictedDatum := OriginalSchemeDescentBaseChange318.datum f (f ∣_ U.1)
  (sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm D

@[expose] def affineHom : Hom
    (OriginalCanonicalDescent318.datum (AffineFaithfullyFlatChart318.map f U.1)
      (AffineOpenChartDescent318.line f U.1 U.2 D))
    (OriginalSchemeDescentBaseChange318.datum f (AffineFaithfullyFlatChart318.map f U.1)
      (sourceAffine f U).fromSpec U.2.fromSpec (AffineFaithfullyFlatChart318.square f U.1 U.2) D) where
  sheafHom := (AffineOpenChartDescent318.comparison f U.1 U.2 D).hom
  commutes := AffineOpenChartDescent318.original_overlap f U.1 U.2 D

/-- The literal original-open reconstruction map is a morphism of the
actual restricted descent data. Its square follows by composing the
proved canonical chart square, affine recovery and original path square. -/
@[expose] def reconstructionHom : Hom
    (OriginalCanonicalDescent318.datum (f ∣_ U.1) (OriginalAffineOpenLines318.line f D U.1 U.2))
    (restrictedDatum f D U) :=
  (OriginalCanonicalDescent318.baseChangeInverse (AffineFaithfullyFlatChart318.map f U.1)
    (f ∣_ U.1) (sourceAffine f U).isoSpec.hom U.2.isoSpec.hom (chart_square f U).symm
    (AffineOpenChartDescent318.line f U.1 U.2 D)).comp
  ((OriginalSchemeDescentBaseChangeMaps318.map (f ∣_ U.1) (sourceAffine f U).isoSpec.hom
    U.2.isoSpec.hom (chart_square f U).symm (affineHom f D U)).comp
  (OriginalDescentBaseChangePath318.hom f (AffineFaithfullyFlatChart318.map f U.1) (f ∣_ U.1)
    (sourceAffine f U).fromSpec U.2.fromSpec (AffineFaithfullyFlatChart318.square f U.1 U.2)
    (sourceAffine f U).isoSpec.hom U.2.isoSpec.hom (chart_square f U).symm
    (sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm
    (sourceAffine f U).isoSpec_hom_fromSpec U.2.isoSpec_hom_fromSpec D))

lemma reconstructionHom_map : (reconstructionHom f D U).sheafHom =
    (AffineOriginalReconstructionSquare318.reconstruction f D U).hom := by
  simp only [reconstructionHom,OriginalCanonicalDescent318.baseChangeInverse,
    OriginalCanonicalDescent318.inverse,Hom.comp,OriginalSchemeDescentBaseChangeMaps318.map,
    affineHom,OriginalDescentBaseChangePath318.hom,AffineOriginalReconstructionSquare318.reconstruction,
    affinePath,sourcePath,Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,
    PullbackSquareTarget318.cover_flip,Category.assoc]

/-- The full pure chart comparison is compatible with the unchanged
original double overlap, before passing to any global equality detector. -/
@[expose] def comparisonHom : Hom
    (OriginalSchemeDescentBaseChange318.datum f (f ∣_ U.1) (sourceOpen f U).ι U.1.ι
      (morphismRestrict_ι f U.1).symm
      (OriginalCanonicalDescent318.datum f (AffineMorphismGlobalLine318.line f D)))
    (restrictedDatum f D U) :=
  (OriginalCanonicalDescent318.baseChange f (f ∣_ U.1) (sourceOpen f U).ι U.1.ι
    (morphismRestrict_ι f U.1).symm (AffineMorphismGlobalLine318.line f D)).comp
  ((OriginalCanonicalDescent318.map (f ∣_ U.1)
    (CalibratedPullbackChartComparison318.comparison f D U).hom).comp (reconstructionHom f D U))

lemma comparisonHom_map : (comparisonHom f D U).sheafHom =
    (AffineOriginalCoverCompatibility318.comparison f D U).hom := by
  simp only [comparisonHom,Hom.comp,OriginalCanonicalDescent318.baseChange,
    OriginalCanonicalDescent318.map,reconstructionHom_map,AffineOriginalCoverCompatibility318.comparison,
    Iso.trans_hom,Iso.app_hom,Functor.mapIso_hom,Category.assoc]
end OriginalLocalRecoveryDescent318
