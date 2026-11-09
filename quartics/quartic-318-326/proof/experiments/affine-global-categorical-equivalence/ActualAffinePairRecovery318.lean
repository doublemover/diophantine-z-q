module
public import AffineMorphismGlobalLine318
public section
noncomputable section
namespace ActualAffinePairRecovery318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineChartAmbientComparison318 AffineChartLocalPairs318
open OpenChartModuleImages318 OpenSheafRestrictionCompatibility318 OpenSheafTransition318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- The whole-open extension recovers the exact originally supplied pair
iso when that whole open is affine, not only its component classes. -/
lemma pair_recovered (U V W : Y.affineOpens) (hU : W.1 ≤ U.1) (hV : W.1 ≤ V.1) :
    ActualChartPairExtension318.pair f D U V W.1 hU hV =
      AffineChartLocalPairs318.pair f D U V W hU hV := by
  apply Iso.ext
  apply AffineBasisModuleMaps318.hom_ext
  intro T s
  rw [ActualChartPairExtension318.pair_affine]
  let Q := AffineSubopenIsoExtension318.image W.1 T
  let hQ := AffineSubopenIsoExtension318.image_le W.1 T
  have hh := component_restrict (overPair f D U V W hU hV) hQ Q.1 le_rfl s
  rw [overPair_restrict] at hh
  change component (overPair f D U V Q (hQ.trans hU) (hQ.trans hV)) Q.1 le_rfl s = _
  rw [hh]
  exact toOver_hom_app (AffineChartLocalPairs318.pair f D U V W hU hV) T.1 s
end ActualAffinePairRecovery318
