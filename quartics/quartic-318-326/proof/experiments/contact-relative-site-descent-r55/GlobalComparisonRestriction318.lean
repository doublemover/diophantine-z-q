module
public import OriginalDoubleOpenCover318
public section
noncomputable section
namespace GlobalComparisonRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOriginalCoverComparison318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (D : OriginalSchemeDescentData318.Datum f) (U : Y.affineOpens)

/-- The restriction of the actual globally glued map is the exact
previously constructed whole-chart map. -/
lemma restricted_hom :
    (Scheme.Modules.restrictFunctor (sourceOpen f U).ι).map
      (AffineMorphismGlobalRecovery318.comparison f D).hom = (comparison f D U).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  have hW : (sourceOpen f U).ι ''ᵁ W ≤ sourceOpen f U := by
    simpa using (sourceOpen f U).ι.image_le_opensRange W
  have hh := AffineMorphismGlobalRecovery318.comparison_component f D U
    ((sourceOpen f U).ι ''ᵁ W) hW s
  change (AffineMorphismGlobalRecovery318.comparison f D).hom.app
      ((sourceOpen f U).ι ''ᵁ W) s = (comparison f D U).hom.app W s
  rw [hh]
  exact OpenSheafRestrictionCompatibility318.toOver_hom_app (comparison f D U) W s

/-- Recovery holds as equality of the original restricted isomorphisms,
including the inverse, rather than as an unrelated local existence result. -/
lemma restricted_iso :
    (Scheme.Modules.restrictFunctor (sourceOpen f U).ι).mapIso
      (AffineMorphismGlobalRecovery318.comparison f D) = comparison f D U :=
  Iso.ext (restricted_hom f D U)

/-- The actual original source pullback of the global map is the exact
pure-pullback chart comparison used for the overlap calculation. -/
lemma pullback_iso :
    (Scheme.Modules.pullback (sourceOpen f U).ι).mapIso
      (AffineMorphismGlobalRecovery318.comparison f D) =
        AffineOriginalCoverCompatibility318.comparison f D U := by
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback (sourceOpen f U).ι).hom.app
    (AffineMorphismGlobalRecovery318.pullbackLine f D))).mp
  have hn := (Scheme.Modules.restrictFunctorIsoPullback (sourceOpen f U).ι).hom.naturality
    (AffineMorphismGlobalRecovery318.comparison f D).hom
  rw [← hn,restricted_hom,← OriginalCoverRestrictionCompatibility318.comparison_eq f D U]
  simp only [PullbackRestrictionCompatibility318.restriction,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
end GlobalComparisonRestriction318
