module
public import ActualTwoDescentOriginalMatchedTensorSquare318
public import RestrictionPullbackCoherence318
public import OpenPushforwardGlobalValue318
public section
noncomputable section
namespace ActualTwoDescentOpenRestrictionAdjointComposition318
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y Z : Scheme.{u}} (j : Y ⟶ X) (k : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k]

/-- The EXACT native composition comparison,not a newly chosen
adjunction-compatible substitute. The baseline producer supplies its unit. -/
lemma composition {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (e : M.restrict j ⟶ N) (d : N.restrict k ⟶ P) :
    (Scheme.Modules.restrictAdjunction (k ≫ j)).homEquiv _ _
      ((Scheme.Modules.restrictFunctorComp k j).hom.app M ≫
        (Scheme.Modules.restrictFunctor k).map e ≫ d)=
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _ e ≫
      (Scheme.Modules.pushforward j).map ((Scheme.Modules.restrictAdjunction k).homEquiv _ _ d) ≫
        (Scheme.Modules.pushforwardComp k j).hom.app P := by
  rw [RestrictionPullbackCoherence318.adjoint_restrict_composition,
    Adjunction.comp_homEquiv,Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]

lemma localMap_adjoint (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward j).obj N) :
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _
      (OpenPushforwardGlobalValue318.localMap j M N f)=f := by
  change (Scheme.Modules.restrictAdjunction j).homEquiv _ _
    (((Scheme.Modules.restrictAdjunction j).homEquiv _ _).symm f)=f
  exact Equiv.apply_symm_apply _ _

/-- Equality transport has the actual pushforward-congruence as mate.
No equality of different chart routes is silently treated as definitional. -/
lemma congr_adjoint {f g : Y ⟶ X} (h : f=g) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : X.Modules) (N : Y.Modules) (e : M.restrict f ⟶ N) :
    (Scheme.Modules.restrictAdjunction g).homEquiv _ _
      ((Scheme.Modules.restrictFunctorCongr h).inv.app M ≫ e)=
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _ e ≫
      (Scheme.Modules.pushforwardCongr h).hom.app N := by
  subst g
  have hr : (Scheme.Modules.restrictFunctorCongr (rfl : f=f)).inv.app M=𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.restrictFunctorCongr_inv_app_app,eqToHom_refl,
      Functor.map_id,Scheme.Modules.Hom.id_app]
  have hp : (Scheme.Modules.pushforwardCongr (rfl : f=f)).hom.app N=𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app,eqToHom_refl,
      Functor.map_id,Scheme.Modules.Hom.id_app]
  rw [hr,hp,Category.id_comp,Category.comp_id]
end ActualTwoDescentOpenRestrictionAdjointComposition318
