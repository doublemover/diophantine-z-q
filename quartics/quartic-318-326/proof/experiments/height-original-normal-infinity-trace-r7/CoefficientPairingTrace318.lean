module
public import TensorCoefficientDuality318
public import Mathlib.RingTheory.Trace.Defs
public section
noncomputable section
namespace CoefficientPairingTrace318
open Module TensorCoefficientDuality318
set_option maxHeartbeats 1800000
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (F : Frame R A ι)
@[expose] def euler : A := ∑ i,F.basis i*F.basis (F.switch i)

/-- The TRUE algebra trace, computed from its actual multiplication
matrix, is the coefficient functional times the concrete Euler element. -/
theorem trace_eq (x : A) : Algebra.trace R A x=F.coefficient (euler F*x) := by
  rw [Algebra.trace_eq_matrix_trace F.basis,Matrix.trace]
  change (∑ i,F.basis.repr (x*F.basis i) i)=_
  simp only [←PerfectCoefficientPairing318.pairing_coordinate F.basis F.switch F.involutive F.coefficient F.pairing]
  rw [euler,Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

variable {B κ : Type*} [CommRing B] [Algebra R B] [Fintype κ] [DecidableEq κ]
  (G : Frame R B κ)
open scoped TensorProduct

theorem euler_tensor : euler (F.tensor G)=euler F ⊗ₜ[R] euler G := by
  change (∑ p : ι × κ,(F.basis p.1 ⊗ₜ[R] G.basis p.2)*
    (F.basis (F.switch p.1) ⊗ₜ[R] G.basis (G.switch p.2)))=_
  simp only [Algebra.TensorProduct.tmul_mul_tmul,Fintype.sum_prod_type,euler,
    TensorProduct.sum_tmul,TensorProduct.tmul_sum]
end CoefficientPairingTrace318
