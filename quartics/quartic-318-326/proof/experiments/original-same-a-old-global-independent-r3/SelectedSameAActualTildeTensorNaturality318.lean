module

public import ScalarExtensionTensor318
public import TildePullback318

/-!
# The actual tilde pullback compares natural tensor maps, not just objects

The tensor model has the genuine algebra scalar action. The right proof
compares both presentations before any assumption on the affine fibre.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings

namespace SelectedSameAActualTildeTensorNaturality318

universe u
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (C B : Type u) [CommRing C] [CommRing B] [Algebra C B]
variable {M N : ModuleCat.{u} C}

theorem tensorEquiv_naturality (e : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap C B)).map e ≫
        (ScalarExtensionTensor318.tensorEquiv (T := B) N).toModuleIso.hom =
      (ScalarExtensionTensor318.tensorEquiv (T := B) M).toModuleIso.hom ≫
        ModuleCat.ofHom (AlgebraTensorModule.lTensor B B e.hom) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    change ScalarExtensionTensor318.tensorEquiv (T := B) N
      ((ModuleCat.extendScalars (algebraMap C B)).map e
        (b ⊗ₜ[C, algebraMap C B] m)) =
      AlgebraTensorModule.lTensor B B e.hom
        (ScalarExtensionTensor318.tensorEquiv (T := B) M (b ⊗ₜ[C, algebraMap C B] m))
    rw [ModuleCat.ExtendScalars.map_tmul, ScalarExtensionTensor318.tensorEquiv_tmul,
      ScalarExtensionTensor318.tensorEquiv_tmul, AlgebraTensorModule.lTensor_tmul] <;> rfl

/-- Actual sheaf comparison, with no condition on the affine morphism. -/
@[expose] def tensorIso (M : ModuleCat.{u} C) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap C B)))).obj
      (tilde (R := CommRingCat.of C) M) ≅
    tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] M)) :=
  (TildePullback318.pullbackIso (CommRingCat.ofHom (algebraMap C B))).app M ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (ScalarExtensionTensor318.tensorEquiv (T := B) M).toModuleIso

/-- This equality is the genuine base-changed sheaf map, with all
coefficient scalar actions reconciled by the same pure-tensor map. -/
theorem tensorIso_naturality (e : M ⟶ N) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap C B)))).map
        ((tilde.functor (CommRingCat.of C)).map e) ≫ (tensorIso C B N).hom =
      (tensorIso C B M).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (AlgebraTensorModule.lTensor B B e.hom)) := by
  have h := (TildePullback318.pullbackIso (CommRingCat.ofHom (algebraMap C B))).hom.naturality e
  simp only [Functor.comp_map, CommRingCat.hom_ofHom] at h
  simp only [tensorIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, h, Category.assoc]
  have hcompose := (tilde.functor (CommRingCat.of B)).map_comp
    ((ModuleCat.extendScalars (algebraMap C B)).map e)
    (ScalarExtensionTensor318.tensorEquiv (T := B) N).toModuleIso.hom
  rw [← hcompose, tensorEquiv_naturality C B, Functor.map_comp]

end SelectedSameAActualTildeTensorNaturality318
