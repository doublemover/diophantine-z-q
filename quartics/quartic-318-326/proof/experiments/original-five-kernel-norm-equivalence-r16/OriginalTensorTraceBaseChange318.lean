module
public import SquareZeroNormTrace318
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace OriginalTensorTraceBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
/-- Multiplication by the ORIGINAL right coefficient is the scalar extension
of the ORIGINAL multiplication map, on the entire tensor algebra. -/
lemma multiplication (s : S) :
    Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ[R] s) = (Algebra.lmul R S s).baseChange A := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a t =>
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simpa only [map_add, hx, hy]
variable [Module.Free R S] [Module.Finite R S]
/-- The original trace commutes with actual tensor extension over ANY base,
including the nonreduced dual-number test ring. -/
lemma trace (s : S) : Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ[R] s) =
    algebraMap R A (Algebra.trace R S s) := by
  rw [Algebra.trace_apply, multiplication, LinearMap.trace_baseChange]
  all_goals rfl
lemma norm (s : S) : Algebra.norm A (1 ⊗ₜ[R] s : A ⊗[R] S) =
    algebraMap R A (Algebra.norm R s) := by
  rw [Algebra.norm_apply, multiplication, LinearMap.det_baseChange]
  all_goals rfl
lemma norm_infinitesimal (e : A) (he : e * e = 0) (s : S) :
    Units.map (Algebra.norm A)
      (InfinitesimalUnitCocycle318.infinitesimal
        (algebraMap A (A ⊗[R] S) e) (SquareZeroNormTrace318.epsilon_square e he) (1 ⊗ₜ[R] s)) =
    InfinitesimalUnitCocycle318.infinitesimal e he (algebraMap R A (Algebra.trace R S s)) := by
  rw [SquareZeroNormTrace318.norm_infinitesimal, trace]
end OriginalTensorTraceBaseChange318
