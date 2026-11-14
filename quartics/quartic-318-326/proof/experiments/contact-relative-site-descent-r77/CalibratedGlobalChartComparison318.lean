module
public import ActualAffinePairRecovery318
public section
noncomputable section
namespace CalibratedGlobalChartComparison318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open AffineChartAmbientComparison318 OpenChartModuleImages318
open OpenSheafRestrictionCompatibility318 OpenSheafTransition318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

abbrev originalDatum := AffineMorphismGlobalLine318.datum f D
abbrev overDatum := OpenSchemeTransition318.overData (originalDatum f D)
abbrev ambientComparison (U : Y.affineOpens) := OpenSchemeGluing318.comparison (originalDatum f D) U
abbrev overComparison (U : Y.affineOpens) := OpenSheafGluing318.overIso (overDatum f D) U

/-- Matching-family gluing recovers the same whole-open transition on
nested original affine charts, without rewriting an intersection by fiat. -/
lemma ambient_nested (U W : Y.affineOpens) (h : W.1 ≤ U.1) :
    schemeRestrict (ambientComparison f D U) h ≪≫
      ActualChartPairExtension318.pair f D U W W.1 h le_rfl = ambientComparison f D W := by
  apply OpenSchemeTransition318.toOver_injective
  rw [OpenSchemeTransition318.toOver_trans,restriction_compatible,
    OpenSchemeGluing318.comparison_toOver,OpenSchemeGluing318.comparison_toOver]
  have hp := congrArg (toOverIso W.1)
    (ActualChartPairRestriction318.pair_restrict f D U W (U.1 ⊓ W.1) W.1
      inf_le_left inf_le_right (le_inf h le_rfl))
  rw [restriction_compatible] at hp
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  let T := V.unop.left
  let ht : T ≤ W.1 := leOfHom V.unop.hom
  change component (toOverIso W.1 (ActualChartPairExtension318.pair f D U W W.1 h le_rfl)) T ht
      (component (restrictIso (overComparison f D U) h) T ht s) =
    component (overComparison f D W) T ht s
  rw [component_restrict]
  have hh := component_restrict ((overDatum f D).transition U W) (le_inf h le_rfl) T ht
    (component (overComparison f D U) T (ht.trans h) s)
  rw [hp] at hh
  rw [hh]
  exact OpenModuleChartRecovery318.evaluate_transition (OpenSheafTransition318.sectionData (overDatum f D))
    U W T (ht.trans h) ht s

/-- Calibrate the gluing chart comparison through that chart's own actual
reconstruction path. This retains a specified iso, not an arbitrary choice. -/
@[expose] def comparison (U : Y.affineOpens) :
    (AffineMorphismGlobalLine318.line f D).object.restrict U.1.ι ≅ (localLine f D U).object :=
  ambientComparison f D U ≪≫ AffineChartAmbientComparison318.comparison f D U U le_rfl

/-- The calibrated original global-to-chart maps respect the exact
reconstructed nested restriction comparisons. -/
lemma comparison_nested (U W : Y.affineOpens) (h : W.1 ≤ U.1) :
    path (AffineMorphismGlobalLine318.line f D).object h ≪≫
      (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso (comparison f D U) ≪≫
        OriginalAffineOpenLines318.restrictionComparison f D U.1 W.1 U.2 W.2 h =
      comparison f D W := by
  have hn := ambient_nested f D U W h
  rw [ActualAffinePairRecovery318.pair_recovered] at hn
  have hc := AffineChartAmbientComparison318.comparison_restrict f D U U W le_rfl h
  have he := congrArg Iso.hom hn
  have hp := congrArg Iso.hom hc
  apply Iso.ext
  simp only [comparison,Iso.trans_hom,Functor.mapIso_hom,Functor.map_comp,Category.assoc]
  have he' : (schemeRestrict (ambientComparison f D U) h).hom ≫
      (AffineChartAmbientComparison318.comparison f D U W h).hom =
    (ambientComparison f D W).hom ≫
      (AffineChartAmbientComparison318.comparison f D W W le_rfl).hom := by
    have hh := congrArg (fun q => q ≫
      (AffineChartAmbientComparison318.comparison f D W W le_rfl).hom) he
    simpa only [AffineChartLocalPairs318.pair,Iso.trans_hom,Iso.symm_hom,
      Category.assoc,Iso.inv_hom_id_assoc] using hh
  rw [← he']
  simp only [schemeRestrict,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Category.assoc]
  have hp' : (path (ambient f D U) h).hom ≫
      (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
        (AffineChartAmbientComparison318.comparison f D U U le_rfl).hom ≫
          (OriginalAffineOpenLines318.restrictionComparison f D U.1 W.1 U.2 W.2 h).hom =
    (AffineChartAmbientComparison318.comparison f D U W h).hom := by
    simpa only [Iso.trans_hom,Functor.mapIso_hom,Category.assoc] using hp
  rw [← hp']
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
end CalibratedGlobalChartComparison318
