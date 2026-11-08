module
public import DifferentialFunctor318
public import LocalizedKaehlerFrame318
public import Mathlib.RingTheory.Kaehler.Polynomial
public section
noncomputable section
namespace EtaleDifferentialFrame318
open KaehlerDifferential
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- Reconstructed universal-differential cancellation for an actual algebra equivalence. -/
theorem map_equiv_symm (f : S ≃ₐ[R] T) (ω : KaehlerDifferential R T) :
    AlgHomDifferential318.map f.toAlgHom
      (AlgHomDifferential318.map f.symm.toAlgHom ω) = ω := by
  rw [←DifferentialFunctor318.map_comp_apply]
  have h : f.toAlgHom.comp f.symm.toAlgHom = AlgHom.id R T := by
    ext t
    exact f.apply_symm_apply t
  rw [h,DifferentialFunctor318.map_id_apply]

/-- Transport an actual differential frame along an algebra equivalence. -/
@[expose] def ofAlgEquiv (f : S ≃ₐ[R] T)
    (e : KaehlerDifferential R S ≃ₗ[S] S) : KaehlerDifferential R T ≃ₗ[T] T where
  toFun ω := f (e (AlgHomDifferential318.map f.symm.toAlgHom ω))
  invFun t := AlgHomDifferential318.map f.toAlgHom (e.symm (f.symm t))
  left_inv ω := by
    simp only [f.symm_apply_apply,e.symm_apply_apply]
    exact map_equiv_symm f ω
  right_inv t := by
    rw [map_equiv_symm f.symm,e.apply_symm_apply,f.apply_symm_apply]
  map_add' ω η := by simp only [map_add]
  map_smul' t ω := by
    rw [AlgHomDifferential318.map_smul,e.map_smul]
    change f (f.symm t * e (AlgHomDifferential318.map f.symm.toAlgHom ω)) = _
    rw [map_mul,f.apply_symm_apply]
    rfl

variable [Algebra S T] [IsScalarTower R S T]

/-- Actual formal étaleness transports the whole differential module. -/
@[expose] def ofFormallyEtale [Algebra.FormallyEtale S T]
    (e : KaehlerDifferential R S ≃ₗ[S] S) : KaehlerDifferential R T ≃ₗ[T] T :=
  LocalizedKaehlerFrame318.etaleFrame e

end EtaleDifferentialFrame318
