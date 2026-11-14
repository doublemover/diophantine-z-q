module
public import AffineAmbientMapNaturality318
public section
noncomputable section
namespace AffineGlobalDescendedMap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open CalibratedGlobalChartComparison318
set_option maxHeartbeats 3000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {D E : OriginalSchemeDescentData318.Datum f}
  (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E)

@[expose] def overMap : OpenSheafDescentMaps318.Map (overDatum f D) (overDatum f E) where
  app U := (SheafOfModules.overFunctor Y.ringCatSheaf U.1).map (AffineAmbientMapNaturality318.map f k U)
  compatible U V := by
    rw [LocalChartMorphismNormalization318.restrictHom_global,
      LocalChartMorphismNormalization318.restrictHom_global]
    exact LocalChartCategoricalDescent318.toOver_square (U.1 ⊓ V.1)
      (AffineAmbientMapNaturality318.map f k U) (AffineAmbientMapNaturality318.map f k V)
      (ActualChartPairExtension318.pair f D U V (U.1 ⊓ V.1) inf_le_left inf_le_right)
      (ActualChartPairExtension318.pair f E U V (U.1 ⊓ V.1) inf_le_left inf_le_right)
      (AffineAmbientMapNaturality318.whole_pair_natural f k U V (U.1 ⊓ V.1) inf_le_left inf_le_right)

/-- The actual global base-line map obtained from the original descended
chart maps and the proved original whole-intersection squares. -/
@[expose] def map : (AffineMorphismGlobalLine318.line f D).object ⟶
    (AffineMorphismGlobalLine318.line f E).object :=
  OpenSheafDescentMaps318.gluedMap (overMap f k)

lemma ambient_square (U : Y.affineOpens) :
    (Scheme.Modules.restrictFunctor U.1.ι).map (map f k) ≫ (ambientComparison f E U).hom =
      (ambientComparison f D U).hom ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map (AffineAmbientMapNaturality318.map f k U) := by
  have hh := congrArg ((Scheme.Modules.overEquiv U.1).functor.map)
    (OpenSheafDescentMaps318.chart_square (overMap f k) U)
  have hn := (Scheme.Modules.overFunctorEquiv U.1).inv.naturality (map f k)
  have ha := (Scheme.Modules.overFunctorEquiv U.1).hom.naturality (AffineAmbientMapNaturality318.map f k U)
  simp only [Functor.comp_map] at hn ha
  simp only [Functor.map_comp] at hh
  change (Scheme.Modules.restrictFunctor U.1.ι).map (map f k) ≫
      ((Scheme.Modules.overFunctorEquiv U.1).inv.app _ ≫
        (Scheme.Modules.overEquiv U.1).functor.map (overComparison f E U).hom ≫
          (Scheme.Modules.overFunctorEquiv U.1).hom.app _) =
    ((Scheme.Modules.overFunctorEquiv U.1).inv.app _ ≫
      (Scheme.Modules.overEquiv U.1).functor.map (overComparison f D U).hom ≫
        (Scheme.Modules.overFunctorEquiv U.1).hom.app _) ≫ _
  rw [← Category.assoc,hn]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((Scheme.Modules.overFunctorEquiv U.1).hom.app _),hh]
  simp only [Category.assoc]
  rw [ha]

lemma calibrated_square (U : Y.affineOpens) :
    (Scheme.Modules.restrictFunctor U.1.ι).map (map f k) ≫ (comparison f E U).hom =
      (comparison f D U).hom ≫ OriginalOpenChartMaps318.map f k U := by
  simp only [comparison,Iso.trans_hom,Category.assoc]
  rw [← Category.assoc,ambient_square,Category.assoc,AffineAmbientMapNaturality318.comparison_natural]

/-- The calibrated square retains the literal original pullback functor. -/
lemma pullback_square (U : Y.affineOpens) :
    (Scheme.Modules.pullback U.1.ι).map (map f k) ≫
      (CalibratedPullbackChartComparison318.comparison f E U).hom =
    (CalibratedPullbackChartComparison318.comparison f D U).hom ≫ OriginalOpenChartMaps318.map f k U := by
  have hn := (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).inv.naturality (map f k)
  simp only [CalibratedPullbackChartComparison318.comparison,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,Category.assoc]
  rw [← Category.assoc,hn,Category.assoc,calibrated_square]
end AffineGlobalDescendedMap318
