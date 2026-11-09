module
public import OpenRestrictionPathNormalization318
public section
noncomputable section
namespace CalibratedPullbackChartComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OpenSheafRestrictionCompatibility318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- The same calibrated global chart map, viewed through the actual
original pullback rather than a newly chosen restriction comparison. -/
@[expose] def comparison (U : Y.affineOpens) :
    (Scheme.Modules.pullback U.1.ι).obj (AffineMorphismGlobalLine318.line f D).object ≅
      (AffineChartAmbientComparison318.localLine f D U).object :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app (AffineMorphismGlobalLine318.line f D).object).symm ≪≫
    CalibratedGlobalChartComparison318.comparison f D U

/-- The original pullback chart maps satisfy the exact normalized nested
comparison equation used by the global covering-line pasting theorem. -/
lemma comparison_nested (U W : Y.affineOpens) (h : W.1 ≤ U.1) :
    (Scheme.Modules.pullback (Y.homOfLE h)).map (comparison f D U).hom ≫
      (OriginalAffineOpenLines318.pullbackComparison f D U.1 W.1 U.2 W.2 h).hom =
    (PullbackPathComposition318.iso (Y.homOfLE h) U.1.ι W.1.ι (Scheme.homOfLE_ι Y h)).hom.app
      (AffineMorphismGlobalLine318.line f D).object ≫ (comparison f D W).hom := by
  let K := (AffineMorphismGlobalLine318.line f D).object
  let R := Scheme.Modules.restrictFunctor (Y.homOfLE h)
  let P := Scheme.Modules.pullback (Y.homOfLE h)
  let c := Scheme.Modules.restrictFunctorIsoPullback (Y.homOfLE h)
  let u := (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app K
  let w := (Scheme.Modules.restrictFunctorIsoPullback W.1.ι).app K
  let e := CalibratedGlobalChartComparison318.comparison f D U
  let d := CalibratedGlobalChartComparison318.comparison f D W
  let t := OriginalAffineOpenLines318.pullbackComparison f D U.1 W.1 U.2 W.2 h
  let q := (PullbackPathComposition318.iso (Y.homOfLE h) U.1.ι W.1.ι (Scheme.homOfLE_ι Y h)).app K
  have hn := c.hom.naturality u.inv
  have he := c.hom.naturality e.hom
  have hp := OpenRestrictionPathNormalization318.comparison_path K h
  have hd := congrArg Iso.hom (CalibratedGlobalChartComparison318.comparison_nested f D U W h)
  change (path K h).hom ≫ R.map u.hom ≫ c.hom.app ((Scheme.Modules.pullback U.1.ι).obj K) ≫ q.hom = w.hom at hp
  change (path K h).hom ≫ R.map e.hom ≫ c.hom.app _ ≫ t.hom = d.hom at hd
  apply (cancel_epi ((path K h).hom ≫ R.map u.hom ≫ c.hom.app ((Scheme.Modules.pullback U.1.ι).obj K))).mp
  change ((path K h).hom ≫ R.map u.hom ≫ c.hom.app _) ≫ P.map (u.inv ≫ e.hom) ≫ t.hom =
    ((path K h).hom ≫ R.map u.hom ≫ c.hom.app _) ≫ q.hom ≫ w.inv ≫ d.hom
  simp only [Functor.map_comp,Category.assoc]
  rw [← Category.assoc (c.hom.app ((Scheme.Modules.pullback U.1.ι).obj K)),← hn]
  simp only [← Functor.map_comp_assoc,Iso.hom_inv_id,Functor.map_id,Category.id_comp]
  rw [← Category.assoc (c.hom.app (K.restrict U.1.ι)),← he]
  have hh := congrArg (fun z => z ≫ w.inv ≫ d.hom) hp
  simp only [Category.assoc,Iso.hom_inv_id_assoc] at hh
  rw [hh]
  exact hd
end CalibratedPullbackChartComparison318
