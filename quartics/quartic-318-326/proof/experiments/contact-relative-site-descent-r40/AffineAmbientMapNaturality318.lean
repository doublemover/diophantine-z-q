module
public import OriginalOpenChartMaps318
public section
noncomputable section
namespace AffineAmbientMapNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineChartAmbientComparison318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {D E : OriginalSchemeDescentData318.Datum f}
  (k : OriginalSchemeDescentBaseChangeMaps318.Hom D E)

@[expose] def map (U : Y.affineOpens) : ambient f D U ⟶ ambient f E U :=
  (Scheme.Modules.pushforward U.1.ι).map (OriginalOpenChartMaps318.map f k U)

lemma comparison_natural (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    (Scheme.Modules.restrictFunctor V.1.ι).map (map f k U) ≫ (comparison f E U V h).hom =
      (comparison f D U V h).hom ≫ OriginalOpenChartMaps318.map f k V := by
  have hn := LocalChartMorphismNormalization318.subchart_natural (opens (Y:=Y))
    (OriginalOpenChartMaps318.map f k) U V.1 h
  simp only [comparison,Iso.trans_hom,Category.assoc]
  rw [← Category.assoc,hn,Category.assoc,OriginalOpenChartMaps318.restriction_natural]

lemma pair_natural (U V W : Y.affineOpens) (hU : W.1 ≤ U.1) (hV : W.1 ≤ V.1) :
    (Scheme.Modules.restrictFunctor W.1.ι).map (map f k U) ≫
        (AffineChartLocalPairs318.pair f E U V W hU hV).hom =
      (AffineChartLocalPairs318.pair f D U V W hU hV).hom ≫
        (Scheme.Modules.restrictFunctor W.1.ι).map (map f k V) := by
  apply (cancel_mono (comparison f E V W hV).hom).mp
  simp only [AffineChartLocalPairs318.pair,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [comparison_natural f k V W hV,Iso.inv_hom_id_assoc,comparison_natural]

lemma overPair_natural (U V W : Y.affineOpens) (hU : W.1 ≤ U.1) (hV : W.1 ≤ V.1) :
    (SheafOfModules.overFunctor Y.ringCatSheaf W.1).map (map f k U) ≫
      (AffineChartLocalPairs318.overPair f E U V W hU hV).hom =
    (AffineChartLocalPairs318.overPair f D U V W hU hV).hom ≫
      (SheafOfModules.overFunctor Y.ringCatSheaf W.1).map (map f k V) :=
  LocalChartCategoricalDescent318.toOver_square W.1 (map f k U) (map f k V)
    (AffineChartLocalPairs318.pair f D U V W hU hV)
    (AffineChartLocalPairs318.pair f E U V W hU hV) (pair_natural f k U V W hU hV)

/-- Compatibility extends to the whole original intersection, using all
its affine subopens and the unchanged original extension components. -/
lemma whole_pair_natural (U V : Y.affineOpens) (Z : Y.Opens) (hU : Z ≤ U.1) (hV : Z ≤ V.1) :
    (Scheme.Modules.restrictFunctor Z.ι).map (map f k U) ≫
      (ActualChartPairExtension318.pair f E U V Z hU hV).hom =
    (ActualChartPairExtension318.pair f D U V Z hU hV).hom ≫
      (Scheme.Modules.restrictFunctor Z.ι).map (map f k V) := by
  apply AffineBasisModuleMaps318.hom_ext
  intro T s
  change (ActualChartPairExtension318.pair f E U V Z hU hV).hom.app T.1
      ((map f k U).app (Z.ι ''ᵁ T.1) s) =
    (map f k V).app (Z.ι ''ᵁ T.1)
      ((ActualChartPairExtension318.pair f D U V Z hU hV).hom.app T.1 s)
  rw [ActualChartPairExtension318.pair_affine,ActualChartPairExtension318.pair_affine]
  let Q := AffineSubopenIsoExtension318.image Z T
  have hh := overPair_natural f k U V Q
    ((AffineSubopenIsoExtension318.image_le Z T).trans hU)
    ((AffineSubopenIsoExtension318.image_le Z T).trans hV)
  exact congrArg (fun z => OpenSheafDescentMaps318.componentHom z Q.1 le_rfl s) hh
end AffineAmbientMapNaturality318
