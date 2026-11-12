module
public import OriginalCoverComparisonPasting318
public section
noncomputable section
namespace OpenRestrictionPathNormalization318
open AlgebraicGeometry CategoryTheory Opposite OpenSheafRestrictionCompatibility318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens} (h : W ≤ U)

/-- The original ambient restriction path and original nested collapse
are inverses on the unchanged sheaf, checked on actual section maps. -/
lemma path_collapse : (path M h).hom ≫
    (RestrictionTransitionPasting318.collapse (X.homOfLE h) U.ι W.ι (Scheme.homOfLE_ι X h)).hom.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro T
  ext s
  simp only [path,RestrictionTransitionPasting318.collapse,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,NatTrans.comp_app,Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply,
    Scheme.Modules.restrictFunctorComp_hom_app_app,Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,Scheme.Modules.Hom.id_app,ConcreteCategory.id_apply]
  simp only [← M.presheaf.map_comp_apply]
  change M.presheaf.map (𝟙 _) s = s
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]

/-- The actual open restriction path converts exactly to the original
pullback composition path, including both original adjunction comparisons. -/
lemma comparison_path :
    (path M h).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)).hom.app
          ((Scheme.Modules.pullback U.ι).obj M) ≫
            (PullbackPathComposition318.iso (X.homOfLE h) U.ι W.ι (Scheme.homOfLE_ι X h)).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M := by
  rw [RestrictionTransitionPasting318.comparison_path,← Category.assoc,path_collapse,Category.id_comp]
end OpenRestrictionPathNormalization318
