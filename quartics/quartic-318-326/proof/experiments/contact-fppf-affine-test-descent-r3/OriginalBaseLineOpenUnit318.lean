module
public import OriginalBaseLineAffineUnit318
public section
noncomputable section
namespace OriginalBaseLineOpenUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOriginalCoverComparison318
set_option maxHeartbeats 3200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (L : Line Y) (U : Y.affineOpens)
abbrev datum := OriginalCanonicalDescent318.datum f L
abbrev basePath := (PullbackPathComposition318.iso U.2.isoSpec.hom U.2.fromSpec U.1.ι
  U.2.isoSpec_hom_fromSpec).app L.object

@[expose] def localIso :
    (OriginalAffineOpenLines318.line f (datum f L) U.1 U.2).object ≅
      (Scheme.Modules.pullback U.1.ι).obj L.object :=
  (Scheme.Modules.pullback U.2.isoSpec.hom).mapIso (OriginalBaseLineAffineUnit318.iso f L U) ≪≫
    basePath L U

/-- The original open unit retains the exact global covering comparison,
by canonical pasting of the original affine-chart and open-chart squares. -/
lemma localIso_cover :
    (Scheme.Modules.pullback (f ∣_ U.1)).map (localIso f L U).hom =
      (AffineOriginalReconstructionSquare318.reconstruction f (datum f L) U).hom ≫
        (ActualDescentBaseChangeDiagram318.coverComparison f (f ∣_ U.1) (sourceOpen f U).ι U.1.ι
          (morphismRestrict_ι f U.1).symm).hom.app L.object := by
  let c := ActualDescentBaseChangeDiagram318.coverComparison (AffineFaithfullyFlatChart318.map f U.1)
    (f ∣_ U.1) (sourceAffine f U).isoSpec.hom U.2.isoSpec.hom (chart_square f U).symm
  have hn := c.hom.naturality (OriginalBaseLineAffineUnit318.iso f L U).hom
  simp only [Functor.comp_map] at hn
  have hp := SheafComparisonPasting318.cover_pasting f (AffineFaithfullyFlatChart318.map f U.1)
    (f ∣_ U.1) (sourceAffine f U).fromSpec U.2.fromSpec (AffineFaithfullyFlatChart318.square f U.1 U.2)
    (sourceAffine f U).isoSpec.hom U.2.isoSpec.hom (chart_square f U).symm
    (sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm
    (sourceAffine f U).isoSpec_hom_fromSpec U.2.isoSpec_hom_fromSpec L.object
  simp only [localIso,Iso.trans_hom,Functor.mapIso_hom,Functor.map_comp,
    AffineOriginalReconstructionSquare318.reconstruction,affinePath,sourcePath,
    Iso.app_hom,PullbackSquareTarget318.cover_flip,Category.assoc]
  rw [hp,← Functor.map_comp_assoc,← OriginalBaseLineAffineUnit318.iso_cover]
  have hn' := congrArg (fun z => c.inv.app
    (OriginalBaseLineAffineUnit318.reconstructed f L U).object ≫ z ≫
      (Scheme.Modules.pullback (f ∣_ U.1)).map (basePath L U).hom) hn
  simpa only [Category.assoc,Iso.inv_hom_id_app_assoc] using hn'.symm

/-- The original arbitrary base line and its reconstructed canonical
line are compared on the entire original affine base chart. -/
@[expose] def comparison :
    (Scheme.Modules.pullback U.1.ι).obj (AffineMorphismGlobalLine318.line f (datum f L)).object ≅
      (Scheme.Modules.pullback U.1.ι).obj L.object :=
  CalibratedPullbackChartComparison318.comparison f (datum f L) U ≪≫ localIso f L U

lemma comparison_cover :
    (ActualDescentBaseChangeDiagram318.coverComparison f (f ∣_ U.1) (sourceOpen f U).ι U.1.ι
      (morphismRestrict_ι f U.1).symm).hom.app (AffineMorphismGlobalLine318.line f (datum f L)).object ≫
      (Scheme.Modules.pullback (f ∣_ U.1)).map (comparison f L U).hom =
    (Scheme.Modules.pullback (sourceOpen f U).ι).map
      (AffineMorphismGlobalRecovery318.comparison f (datum f L)).hom ≫
        (ActualDescentBaseChangeDiagram318.coverComparison f (f ∣_ U.1) (sourceOpen f U).ι U.1.ι
          (morphismRestrict_ι f U.1).symm).hom.app L.object := by
  have he := congrArg Iso.hom (GlobalComparisonRestriction318.pullback_iso f (datum f L) U)
  simp only [Functor.mapIso_hom] at he
  rw [he]
  simp only [comparison,Iso.trans_hom,Functor.map_comp,Category.assoc]
  rw [localIso_cover] <;> rfl
end OriginalBaseLineOpenUnit318
