module
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace SymmetricScalarChange318
open scoped TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  (M : Type w) [AddCommGroup M] [Module R M]
local notation "A" => SymmetricAlgebra R M
local notation "T" => SymmetricAlgebra B (B ⊗[R] M)
local instance : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
local instance : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl

@[expose] def forwardGenerator : M →ₗ[R] T :=
  ((SymmetricAlgebra.ι B (B ⊗[R] M)).restrictScalars R).comp
    (TensorProduct.mk R B M 1)
@[expose] def forward : (B ⊗[R] A) →ₐ[B] T :=
  AlgHom.liftEquiv R B A T (SymmetricAlgebra.lift (forwardGenerator R B M))
@[expose] def backwardGenerator : (B ⊗[R] M) →ₗ[B] (B ⊗[R] A) :=
  ((TensorProduct.mk R B A 1).comp (SymmetricAlgebra.ι R M)).liftBaseChange B
@[expose] def backward : T →ₐ[B] (B ⊗[R] A) :=
  SymmetricAlgebra.lift (backwardGenerator R B M)

lemma forward_tmul_generator (b : B) (m : M) :
    forward R B M (b ⊗ₜ[R] SymmetricAlgebra.ι R M m) =
      b • SymmetricAlgebra.ι B (B ⊗[R] M) (1 ⊗ₜ[R] m) := by
  rw [forward,AlgHom.liftEquiv_tmul,SymmetricAlgebra.lift_ι_apply]
  rfl

lemma backward_generator_tmul (b : B) (m : M) :
    backward R B M (SymmetricAlgebra.ι B (B ⊗[R] M) (b ⊗ₜ[R] m)) =
      b ⊗ₜ[R] SymmetricAlgebra.ι R M m := by
  rw [backward,SymmetricAlgebra.lift_ι_apply,backwardGenerator,LinearMap.liftBaseChange_tmul]
  change b • ((1 : B) ⊗ₜ[R] SymmetricAlgebra.ι R M m) = _
  rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

lemma backward_forward : (backward R B M).comp (forward R B M) = AlgHom.id B (B ⊗[R] A) := by
  apply Algebra.TensorProduct.ext_ring
  apply SymmetricAlgebra.algHom_ext
  ext m
  change backward R B M (forward R B M (1 ⊗ₜ[R] SymmetricAlgebra.ι R M m)) =
    1 ⊗ₜ[R] SymmetricAlgebra.ι R M m
  rw [forward_tmul_generator,one_smul,backward_generator_tmul]

lemma forward_backward : (forward R B M).comp (backward R B M) = AlgHom.id B T := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro z
  change forward R B M (backward R B M (SymmetricAlgebra.ι B (B ⊗[R] M) z)) =
    SymmetricAlgebra.ι B (B ⊗[R] M) z
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      rw [backward_generator_tmul,forward_tmul_generator]
      rw [← map_smul]
      congr 1
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Canonical symmetric-algebra coefficient comparison with both literal
pure-generator formulas. This is a universal-property construction over
arbitrary coefficient algebras, with no flatness or basis hypotheses. -/
@[expose] def equivalence : (B ⊗[R] A) ≃ₐ[B] T where
  __ := forward R B M
  invFun := backward R B M
  left_inv x := DFunLike.congr_fun (backward_forward R B M) x
  right_inv x := DFunLike.congr_fun (forward_backward R B M) x
end SymmetricScalarChange318
