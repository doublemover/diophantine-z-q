module
public import SelectedIntegralSectionLine318
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
open scoped TensorProduct
open SelectedIntegralSectionLine318

namespace SelectedNoetherDiagonalTrace318

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
local notation "T" => A ⊗[R] A

/-- Actual evaluation of a tensor against the R-linear functional
in the right factor, with multiplication by the left factor. -/
@[expose] def action (ell : A →ₗ[R] R) (z : T) : A →ₗ[R] A :=
  ((scalarEval ell).restrictScalars R).comp
    ((Algebra.lmul R T z).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T).toLinearMap)

theorem action_apply (ell : A →ₗ[R] R) (z : T) (a : A) :
    action ell z a = scalarEval ell (z*((1:A) ⊗ₜ[R] a)) := rfl

theorem action_zero (ell : A →ₗ[R] R) : action ell (0:T) = 0 := by
  ext a
  simp only [action_apply,zero_mul,map_zero,LinearMap.zero_apply]

theorem action_add (ell : A →ₗ[R] R) (z w : T) :
    action ell (z+w) = action ell z + action ell w := by
  ext a
  simp only [action_apply,add_mul,map_add,LinearMap.add_apply]

/-- Pure tensors act by an honest rank-one linear map, not an
arbitrarily chosen change-of-basis for trace. -/
theorem action_tmul (ell : A →ₗ[R] R) (a b : A) :
    action ell (a ⊗ₜ[R] b) = (ell.comp (Algebra.lmul R A b)).smulRight a := by
  ext x
  change scalarEval ell ((a ⊗ₜ[R] b)*((1:A) ⊗ₜ[R] x)) = ell (b*x) • a
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,scalarEval_tmul,Algebra.smul_def]

/-- Equality of the left and right actions on z implies that this
operator is multiplication by precisely its value at 1. -/
theorem action_of_diagonal (ell : A →ₗ[R] R) (z : T)
    (diag : ∀ a : A, z*((1:A) ⊗ₜ[R] a) = (a ⊗ₜ[R] (1:A))*z) :
    action ell z = Algebra.lmul R A (scalarEval ell z) := by
  ext a
  change scalarEval ell (z*((1:A) ⊗ₜ[R] a)) = scalarEval ell z * a
  have hsm : a • z = (a ⊗ₜ[R] (1:A))*z := by
    rw [Algebra.smul_def,Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply]
  rw [diag a,← hsm,map_smul,smul_eq_mul,mul_comm]

variable [Module.Free R A] [Module.Finite R A]

/-- The trace of this tensor operator is the given linear functional
on the literal multiplication of the tensor. Valid for arbitrary
finite free commutative algebras, even without generic separability. -/
theorem action_trace (ell : A →ₗ[R] R) (z : T) :
    LinearMap.trace R A (action ell z) = ell (Algebra.TensorProduct.lmul' R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [action_zero,map_zero]
  | add z w hz hw => simp only [action_add,map_add,hz,hw]
  | tmul a b =>
    rw [action_tmul,LinearMap.trace_smulRight,Algebra.TensorProduct.lmul'_apply_tmul]
    change ell (b*a) = ell (a*b)
    rw [mul_comm]

/-- Direct Noether-different inclusion into the trace image, in the
direction actually needed by the height proof. The witness is the
actual integral contraction of z; there is no division by its degree. -/
theorem M_times_Hom_of_diagonal (M : R) (z : T)
    (diag : ∀ a : A, z*((1:A) ⊗ₜ[R] a) = (a ⊗ₜ[R] (1:A))*z)
    (multiply : Algebra.TensorProduct.lmul' R z = algebraMap R A M)
    (ell : A →ₗ[R] R) :
    M • ell = Algebra.traceForm R A (scalarEval ell z) := by
  ext a
  change M*ell a = Algebra.trace R A (scalarEval ell z * a)
  let za := z*((1:A) ⊗ₜ[R] a)
  have hza (b : A) : za*((1:A) ⊗ₜ[R] b) = (b ⊗ₜ[R] (1:A))*za := by
    calc
      _ = (z*((1:A) ⊗ₜ[R] b))*((1:A) ⊗ₜ[R] a) := by dsimp [za]; ac_rfl
      _ = _ := by rw [diag b]; exact mul_assoc _ _ _
  have he : scalarEval ell za = scalarEval ell z*a :=
    congrArg (fun F : A →ₗ[R] A => F a) (action_of_diagonal ell z diag)
  calc
    _ = ell (Algebra.TensorProduct.lmul' R za) := by
      change M*ell a = ell (Algebra.TensorProduct.lmul' R (z*((1:A) ⊗ₜ[R] a)))
      rw [map_mul,multiply,Algebra.TensorProduct.lmul'_apply_tmul,one_mul,
        ← Algebra.smul_def,map_smul,smul_eq_mul]
    _ = LinearMap.trace R A (action ell za) := (action_trace ell za).symm
    _ = _ := by
      rw [action_of_diagonal ell za hza,he,Algebra.trace_apply]

end SelectedNoetherDiagonalTrace318

#print axioms SelectedNoetherDiagonalTrace318.action_trace
#print axioms SelectedNoetherDiagonalTrace318.M_times_Hom_of_diagonal
