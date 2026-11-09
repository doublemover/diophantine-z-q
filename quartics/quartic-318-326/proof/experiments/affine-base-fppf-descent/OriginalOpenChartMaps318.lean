module
public import GlobalAffineLineFaithfulness318
public section
noncomputable section
namespace OriginalOpenChartMaps318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 3000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {D E : Datum f} (k : Hom D E)

/-- The original affine descended map, with its exact section-ring algebra. -/
@[expose] def affineMap (U : Y.affineOpens) :
    (AffineOpenChartDescent318.line f U.1 U.2 D).object ⟶
      (AffineOpenChartDescent318.line f U.1 U.2 E).object := by
  letI := AffineFaithfullyFlatChart318.algebra f U.1
  letI : Module.FaithfullyFlat Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) :=
    AffineFaithfullyFlatChart318.module_faithfullyFlat f U.1 U.2
  exact ActualAffineDescendedMaps318.map (AffineOpenChartDescent318.mapDatum f U.1 U.2 k)

@[expose] def map (U : Y.affineOpens) :
    (OriginalAffineOpenLines318.line f D U.1 U.2).object ⟶
      (OriginalAffineOpenLines318.line f E U.1 U.2).object :=
  (Scheme.Modules.pullback U.2.isoSpec.hom).map (affineMap f k U)

lemma affineMap_cover (U : Y.affineOpens) :
    (Scheme.Modules.pullback (AffineFaithfullyFlatChart318.map f U.1)).map (affineMap f k U) ≫
      (AffineOpenChartDescent318.comparison f U.1 U.2 E).hom =
    (AffineOpenChartDescent318.comparison f U.1 U.2 D).hom ≫
      (Scheme.Modules.pullback (AffineFaithfullyFlatChart318.source f U.1 U.2)).map k.sheafHom := by
  letI := AffineFaithfullyFlatChart318.algebra f U.1
  letI : Module.FaithfullyFlat Γ(Y,U.1) Γ(X,f ⁻¹ᵁ U.1) :=
    AffineFaithfullyFlatChart318.module_faithfullyFlat f U.1 U.2
  exact ActualAffineDescendedMaps318.map_commutes (AffineOpenChartDescent318.mapDatum f U.1 U.2 k)

lemma pullback_natural (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    (Scheme.Modules.pullback (Y.homOfLE h)).map (map f k U) ≫
      (OriginalAffineOpenLines318.pullbackComparison f E U.1 V.1 U.2 V.2 h).hom =
    (OriginalAffineOpenLines318.pullbackComparison f D U.1 V.1 U.2 V.2 h).hom ≫ map f k V := by
  let q := ActualDescentBaseChangeDiagram318.coverComparison U.2.isoSpec.hom V.2.isoSpec.hom
    (Y.homOfLE h) (AffineOpenChartRefinement318.baseMap U.1 V.1 h)
    (OriginalAffineOpenLines318.chart_square U.1 V.1 U.2 V.2 h)
  have hn := q.hom.naturality (affineMap f k U)
  simp only [Functor.comp_map] at hn
  have hc := AffineOpenChartNaturality318.comparison_natural f U.1 V.1 U.2 V.2 h k
  change (Scheme.Modules.pullback (Y.homOfLE h)).map (map f k U) ≫
      q.hom.app _ ≫ (Scheme.Modules.pullback V.2.isoSpec.hom).map
        (AffineOpenChartComparison318.comparison f U.1 V.1 U.2 V.2 h E).hom =
    q.hom.app _ ≫ (Scheme.Modules.pullback V.2.isoSpec.hom).map
      (AffineOpenChartComparison318.comparison f U.1 V.1 U.2 V.2 h D).hom ≫ map f k V
  rw [← Category.assoc,hn,Category.assoc,← Functor.map_comp,hc,Functor.map_comp]

lemma restriction_natural (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map (map f k U) ≫
      (OriginalAffineOpenLines318.restrictionComparison f E U.1 V.1 U.2 V.2 h).hom =
    (OriginalAffineOpenLines318.restrictionComparison f D U.1 V.1 U.2 V.2 h).hom ≫ map f k V := by
  have hn := (Scheme.Modules.restrictFunctorIsoPullback (Y.homOfLE h)).hom.naturality (map f k U)
  simp only [OriginalAffineOpenLines318.restrictionComparison,Iso.trans_hom,Iso.app_hom,Category.assoc]
  rw [← Category.assoc,hn,Category.assoc,pullback_natural]

/-- The original reconstructed open-chart maps recover the original
covering-line morphism through the same displayed reconstruction isos. -/
lemma reconstruction_natural (U : Y.affineOpens) :
    (Scheme.Modules.pullback (f ∣_ U.1)).map (map f k U) ≫
      (AffineOriginalReconstructionSquare318.reconstruction f E U).hom =
    (AffineOriginalReconstructionSquare318.reconstruction f D U).hom ≫
      (Scheme.Modules.pullback (AffineOriginalCoverComparison318.sourceOpen f U).ι).map k.sheafHom := by
  let c := ActualDescentBaseChangeDiagram318.coverComparison U.2.isoSpec.hom
    (AffineOriginalCoverComparison318.sourceAffine f U).isoSpec.hom (f ∣_ U.1)
    (AffineFaithfullyFlatChart318.map f U.1) (AffineOriginalCoverComparison318.chart_square f U)
  let q := PullbackPathComposition318.iso (AffineOriginalCoverComparison318.sourceAffine f U).isoSpec.hom
    (AffineOriginalCoverComparison318.sourceAffine f U).fromSpec
    (AffineOriginalCoverComparison318.sourceOpen f U).ι
    (AffineOriginalCoverComparison318.sourceAffine f U).isoSpec_hom_fromSpec
  have hn := c.hom.naturality (affineMap f k U)
  have hp := q.hom.naturality k.sheafHom
  simp only [Functor.comp_map] at hn hp
  simp only [AffineOriginalReconstructionSquare318.reconstruction,
    AffineOriginalCoverComparison318.affinePath,AffineOriginalCoverComparison318.sourcePath,
    Iso.trans_hom,Iso.app_hom,Functor.mapIso_hom,Category.assoc]
  rw [← Category.assoc,hn,Category.assoc,← Functor.map_comp_assoc,affineMap_cover,Functor.map_comp]
  simp only [Category.assoc]
  rw [hp]
end OriginalOpenChartMaps318
