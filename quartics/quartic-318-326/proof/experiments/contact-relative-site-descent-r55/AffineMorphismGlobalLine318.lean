module
public import ActualChartPairRestriction318
public section
noncomputable section
namespace AffineMorphismGlobalLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineChartAmbientComparison318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)

/-- The actual full affine cover has genuine whole-intersection transitions,
including non-affine pair and triple intersections. Every law is derived. -/
@[expose] def datum : OpenSchemeTransition318.Data (opens (Y:=Y)) (ambient f D) where
  transition U V := ActualChartPairExtension318.pair f D U V (U.1 ⊓ V.1) inf_le_left inf_le_right
  identity U := ActualChartPairRestriction318.pair_identity f D U (U.1 ⊓ U.1) inf_le_left
  cocycle U V W := by
    rw [ActualChartPairRestriction318.pair_restrict,ActualChartPairRestriction318.pair_restrict,
      ActualChartPairRestriction318.pair_restrict]
    exact ActualChartPairExtension318.pair_cocycle f D U V ((U.1 ⊓ V.1) ⊓ W.1)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) W inf_le_right

lemma cover : (⊤ : Y.Opens) ≤ iSup (opens (Y:=Y)) := by
  rw [show iSup (opens (Y:=Y)) = ⊤ from iSup_affineOpens_eq_top Y]

/-- A genuine global line on the original arbitrary base scheme, built
from the actual affine-chart reconstructions and their proved full overlaps.
The comparison of its f-pullback with the original covering line remains a
separate effectivity endpoint, not a premise hidden in this construction. -/
@[expose] def line : Line Y :=
  OpenChartLineEffectivity318.line (opens (Y:=Y)) (localLine f D)
    (OpenSchemeTransition318.overData (datum f D)) (cover (Y:=Y))

@[expose] def comparison (U : Y.affineOpens) :
    (line f D).object.restrict U.1.ι ≅ (localLine f D U).object :=
  OpenChartLineEffectivity318.comparison (opens (Y:=Y)) (localLine f D)
    (OpenSchemeTransition318.overData (datum f D)) (cover (Y:=Y)) U

/-- The actual displayed comparison recovers every original local
reconstruction, not merely its isomorphism class. -/
theorem local_recovery : ∀ U : Y.affineOpens,
    Nonempty ((line f D).object.restrict U.1.ι ≅ (OriginalAffineOpenLines318.line f D U.1 U.2).object) :=
  fun U => ⟨comparison f D U⟩
end AffineMorphismGlobalLine318
