module
public import FourRootIntegralDuality318
public import CoefficientPairingTrace318
public import FourRootOrderSigns318
public section
noncomputable section
namespace FourRootTraceCoefficient318
open QuadraticPresentation318 QuadraticIntegralDuality318 CoefficientPairingTrace318
open scoped TensorProduct
set_option maxHeartbeats 1800000
variable {R : Type*} [CommRing R]

theorem root_basis_zero (a : R) : (rootFrame a).basis 0=1 := by
  simp [rootFrame,Module.Basis.map_apply]
theorem root_basis_one (a : R) : (rootFrame a).basis 1=AdjoinRoot.root (polynomial a) := by
  simp [rootFrame,Module.Basis.map_apply]

theorem root_euler (a : R) : euler (rootFrame a)= (2 : R) • AdjoinRoot.root (polynomial a) := by
  rw [euler,Fin.sum_univ_two]
  change (rootFrame a).basis 0*(rootFrame a).basis 1+
    (rootFrame a).basis 1*(rootFrame a).basis 0=_
  rw [root_basis_zero,root_basis_one,one_mul,mul_one,two_smul]

variable (a : Fin 4 → R)
@[expose] def rootProduct : FourRootOrder318.Order a :=
  ((AdjoinRoot.root (polynomial (a 0)) ⊗ₜ[R] AdjoinRoot.root (polynomial (a 1))) ⊗ₜ[R]
    (AdjoinRoot.root (polynomial (a 2)) ⊗ₜ[R] AdjoinRoot.root (polynomial (a 3))))

theorem rootProduct_eq : rootProduct a=∏ i : Fin 4,FourRootOrderSigns318.generator a i := by
  simp [rootProduct,Fin.prod_univ_succ,FourRootOrderSigns318.generator,
    Algebra.TensorProduct.one_def,Algebra.TensorProduct.tmul_mul_tmul]

theorem actual_euler : euler (FourRootIntegralDuality318.frame a)= (16 : R) • rootProduct a := by
  unfold FourRootIntegralDuality318.frame
  rw [euler_tensor,euler_tensor,euler_tensor,root_euler,root_euler,root_euler,root_euler]
  norm_num [TensorProduct.smul_tmul_smul,smul_smul,rootProduct]

/-- Literal algebra trace of the actual rank16 four-root order, valid
also when2 or roots vanish in the coefficient ring. -/
theorem trace_eq (x : FourRootOrder318.Order a) :
    Algebra.trace R (FourRootOrder318.Order a) x=
      FourRootIntegralDuality318.coefficient a (((16 : R) • rootProduct a)*x) := by
  rw [CoefficientPairingTrace318.trace_eq (FourRootIntegralDuality318.frame a),actual_euler]
  rfl

theorem trace_eq_generators (x : FourRootOrder318.Order a) :
    Algebra.trace R (FourRootOrder318.Order a) x=
      FourRootIntegralDuality318.coefficient a
        (((16 : R) • (∏ i : Fin 4,FourRootOrderSigns318.generator a i))*x) := by
  rw [trace_eq,rootProduct_eq]
end FourRootTraceCoefficient318
