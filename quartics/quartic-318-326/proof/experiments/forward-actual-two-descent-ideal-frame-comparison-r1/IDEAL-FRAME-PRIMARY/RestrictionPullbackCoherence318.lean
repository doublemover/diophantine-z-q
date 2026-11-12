module
public import PullbackUnitComposition318
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
public section
noncomputable section
namespace RestrictionPullbackCoherence318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
lemma adjoint_restrict {M : Y.Modules} {N : X.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ q) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ q := by
  rw [Adjunction.homEquiv_naturality_right]
  change (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app M) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
lemma restrict_unit :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (IdentityCotangent318.pullbackUnitIso f).hom =
        (Scheme.Modules.restrictUnitIso f).hom := by
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [adjoint_restrict, PullbackScalar318.adjoint_unit, Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change f.app U a = (f.appIso (f⁻¹ᵁU)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op a)
  have h : Y.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
      (f.appIso (f⁻¹ᵁU)).hom = f.app U := by
    have h₀ : f.app U ≫ (f.appIso (f⁻¹ᵁU)).inv =
        Y.presheaf.map (homOfLE (f.image_preimage_le U)).op := f.app_appIso_inv U
    rw [← h₀]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun q => q.hom a) h).symm
variable (g : Y ⟶ Z) [IsOpenImmersion g]
lemma restriction_composition_unit (M : Z.Modules) :
    ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f)).unit.app M ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.restrictFunctor f).obj ((Scheme.Modules.restrictFunctor g).obj M)) =
    (Scheme.Modules.restrictAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.restrictFunctorComp f g).hom.app M) := by
  rw [Adjunction.comp_unit_app]
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, Category.comp_id]
  change M.presheaf.map _ ≫ M.presheaf.map _ = M.presheaf.map _ ≫ M.presheaf.map _
  simp only [← Functor.map_comp]
  rfl
lemma adjoint_restrict_composition {M : Z.Modules} {N : X.Modules}
    (q : ((Scheme.Modules.restrictFunctor g) ⋙ (Scheme.Modules.restrictFunctor f)).obj M ⟶ N) :
    (Scheme.Modules.restrictAdjunction (f ≫ g)).homEquiv _ _
      ((Scheme.Modules.restrictFunctorComp f g).hom.app M ≫ q) =
    ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f)).homEquiv _ _ q ≫
      (Scheme.Modules.pushforwardComp f g).hom.app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← restriction_composition_unit f g, Category.assoc]
  have hn : (Scheme.Modules.pushforwardComp f g).hom.app
      ((Scheme.Modules.restrictFunctor f).obj ((Scheme.Modules.restrictFunctor g).obj M)) ≫
        (Scheme.Modules.pushforward (f ≫ g)).map q =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).map q ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N :=
    ((Scheme.Modules.pushforwardComp f g).hom.naturality q).symm
  rw [hn, ← Category.assoc]
lemma adjoint_restrict_component (M : Y.Modules) :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
/-- The actual restriction-to-pullback comparison respects composition with
its original restriction and pullback comparison maps. -/
lemma composition (M : Z.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫
      (Scheme.Modules.pullbackComp f g).inv.app M =
    (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
      (Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
        ((Scheme.Modules.pullback g).obj M) := by
  apply ((Scheme.Modules.restrictAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [adjoint_restrict, adjoint_restrict_composition, Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
      ((Scheme.Modules.pullbackComp f g).inv.app M) =
    (Scheme.Modules.restrictAdjunction g).homEquiv _ _
      ((Scheme.Modules.restrictAdjunction f).homEquiv _ _
        ((Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          ((Scheme.Modules.pullback g).obj M))) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app _
  rw [Adjunction.homEquiv_naturality_left, adjoint_restrict_component, adjoint_restrict]
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  simpa only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.id_obj, Functor.comp_obj] using h.symm
end RestrictionPullbackCoherence318
