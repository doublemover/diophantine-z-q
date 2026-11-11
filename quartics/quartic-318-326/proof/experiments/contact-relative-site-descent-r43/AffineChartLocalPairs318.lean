module
public import AffineChartAmbientComparison318
public section
noncomputable section
namespace AffineChartLocalPairs318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineChartAmbientComparison318 OpenSheafRestrictionCompatibility318 OpenChartModuleImages318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f)
  (U V W : Y.affineOpens) (hU : W.1 ≤ U.1) (hV : W.1 ≤ V.1)

/-- On an affine common subchart, both original local lines are compared
through that same subchart's original reconstruction. -/
@[expose] def pair : (ambient f D U).restrict W.1.ι ≅ (ambient f D V).restrict W.1.ι :=
  comparison f D U W hU ≪≫ (comparison f D V W hV).symm

/-- Restricting the original pair iso to a smaller affine common subchart
gives its own original pair iso. The common reconstruction cancels. -/
lemma pair_restrict (Z : Y.affineOpens) (k : Z.1 ≤ W.1) :
    schemeRestrict (pair f D U V W hU hV) k =
      pair f D U V Z (k.trans hU) (k.trans hV) := by
  have hu := comparison_restrict f D U W Z hU k
  have hv := comparison_restrict f D V W Z hV k
  unfold pair
  rw [← hu, ← hv]
  apply Iso.ext
  simp only [schemeRestrict, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

abbrev overPair := toOverIso W.1 (pair f D U V W hU hV)

lemma overPair_restrict (Z : Y.affineOpens) (k : Z.1 ≤ W.1) :
    OpenSheafTransition318.restrictIso (overPair f D U V W hU hV) k =
      overPair f D U V Z (k.trans hU) (k.trans hV) := by
  rw [← restriction_compatible, pair_restrict]

/-- Original affine component pair maps carry a literal triple cocycle. -/
lemma pair_cocycle (T : Y.affineOpens) (hT : W.1 ≤ T.1) :
    pair f D U V W hU hV ≪≫ pair f D V T W hV hT = pair f D U T W hU hT := by
  apply Iso.ext
  simp only [pair, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
lemma overPair_cocycle (T : Y.affineOpens) (hT : W.1 ≤ T.1) :
    overPair f D U V W hU hV ≪≫ overPair f D V T W hV hT =
      overPair f D U T W hU hT := by
  rw [← OpenSchemeTransition318.toOver_trans,pair_cocycle]

end AffineChartLocalPairs318
