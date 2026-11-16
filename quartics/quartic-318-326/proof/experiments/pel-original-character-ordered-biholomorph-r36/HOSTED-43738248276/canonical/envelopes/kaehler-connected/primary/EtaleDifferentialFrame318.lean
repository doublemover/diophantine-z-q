module
public import ScalarExtensionTensor318
public import DifferentialFunctor318
public import Mathlib.RingTheory.Kaehler.Polynomial
public section
noncomputable section
namespace EtaleDifferentialFrame318
open TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

/-- A normalized differential frame transports across an actual algebra
isomorphism, with the target's ordinary module structure retained. -/
@[expose] def ofAlgEquiv (f : S ≃ₐ[R] T) (e : KaehlerDifferential R S ≃ₗ[S] S) :
    KaehlerDifferential R T ≃ₗ[T] T where
  toFun ω := f (e (AlgHomDifferential318.map f.symm.toAlgHom ω))
  invFun t := AlgHomDifferential318.map f.toAlgHom (e.symm (f.symm t))
  map_add' ω η := by simp only [map_add]
  map_smul' t ω := by
    simp only [AlgHomDifferential318.map_smul,map_smul,smul_eq_mul,map_mul]
    change f (f.symm t) * _ = t * _
    rw [f.apply_symm_apply]
  left_inv ω := by
    simp only [AlgEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    rw [←DifferentialFunctor318.map_comp_apply]
    have h : f.toAlgHom.comp f.symm.toAlgHom=AlgHom.id R T := by ext t;exact f.apply_symm_apply t
    rw [h]
    exact DifferentialFunctor318.map_id_apply ω
  right_inv t := by
    change f (e (AlgHomDifferential318.map f.symm.toAlgHom
      (AlgHomDifferential318.map f.toAlgHom (e.symm (f.symm t)))))=t
    rw [←DifferentialFunctor318.map_comp_apply]
    have h : f.symm.toAlgHom.comp f.toAlgHom=AlgHom.id R S := by ext s;exact f.symm_apply_apply s
    rw [h,DifferentialFunctor318.map_id_apply,LinearEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply]

variable [Algebra S T] [IsScalarTower R S T]
/-- Formally étale scalar extension preserves a genuine free differential
frame; this constructs the linear equivalence rather than assuming rank one. -/
@[expose] def ofFormallyEtale [Algebra.FormallyEtale S T]
    (e : KaehlerDifferential R S ≃ₗ[S] S) : KaehlerDifferential R T ≃ₗ[T] T :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid S T T
end EtaleDifferentialFrame318
