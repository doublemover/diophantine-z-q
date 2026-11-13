module
public import ScalarChangedFiniteDual318
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public section
noncomputable section
namespace ScalarChangedDualNativeExtension318
open CategoryTheory FiniteDualModuleAction318
open scoped TensorProduct
universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (σ : R ≃+* S) (e : A ≃+* B)
  (h : ∀ r, e (algebraMap R A r)=algebraMap S B (σ r))
local notation "M" => ModuleCat.of A (Dual R A)
local notation "V" => ModuleCat.of B (Dual S B)

/-- The restricted target is the native ModuleCat object, not an
unrecorded local scalar instance on the infinity dual. -/
@[expose] def restrictedIso : M ≅ (ModuleCat.restrictScalars e.toRingHom).obj V :=
  LinearEquiv.toModuleIso
    { toFun := ScalarChangedFiniteDual318.equivalence σ e h
      invFun := (ScalarChangedFiniteDual318.equivalence σ e h).symm
      left_inv := (ScalarChangedFiniteDual318.equivalence σ e h).symm_apply_apply
      right_inv := (ScalarChangedFiniteDual318.equivalence σ e h).apply_symm_apply
      map_add' := (ScalarChangedFiniteDual318.equivalence σ e h).map_add
      map_smul' a f := by
        change ScalarChangedFiniteDual318.equivalence σ e h (a • f)=
          e a • ScalarChangedFiniteDual318.equivalence σ e h f
        exact (ScalarChangedFiniteDual318.equivalence σ e h).map_smulₛₗ a f }

/-- Native scalar extension uses the actual adjunction counit.
Its invertibility is supplied by the actual ring-equivalence restriction functor. -/
@[expose] def extensionIso : (ModuleCat.extendScalars e.toRingHom).obj M ≅ V :=
  (ModuleCat.extendScalars e.toRingHom).mapIso (restrictedIso σ e h) ≪≫
    asIso ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).counit.app V)

lemma one_value (f : Dual R A) (b : B) :
    (extensionIso σ e h).hom (1 ⊗ₜ[A,e.toRingHom] f) b=σ (f (e.symm b)) := by
  change ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).counit.app V
    (1 ⊗ₜ[A,e.toRingHom] ((restrictedIso σ e h).hom f))) b=_
  rw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul] <;> rfl

lemma integral_tensor_value (a : A) (f : Dual R A) (b : B) :
    (extensionIso σ e h).hom (e a ⊗ₜ[A,e.toRingHom] f) b=
      σ (f (a*e.symm b)) := by
  have ht : (e a ⊗ₜ[A,e.toRingHom] f :
      (ModuleCat.extendScalars e.toRingHom).obj M)=
        e a • (1 ⊗ₜ[A,e.toRingHom] f) := by
    rw [ModuleCat.ExtendScalars.smul_tmul,mul_one]
  rw [ht,map_smul]
  change (extensionIso σ e h).hom (1 ⊗ₜ[A,e.toRingHom] f) (e a*b)=_
  rw [one_value,map_mul,e.symm_apply_apply]
end ScalarChangedDualNativeExtension318
