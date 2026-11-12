module
public import FiniteProjectiveEvaluationFrame318
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public section
noncomputable section
namespace FiniteProjectiveTensorDual318
open TensorProduct
open scoped BigOperators TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  (S : Type w) [CommRing S] [Algebra R S]

@[expose] def evaluation : P →ₗ[R] (Module.Dual R P →ₗ[R] S) where
  toFun x :=
    { toFun := fun φ => algebraMap R S (φ x)
      map_add' := fun φ ψ => by simp only [LinearMap.add_apply,map_add]
      map_smul' := fun r φ => by simp only [LinearMap.smul_apply,smul_eq_mul,map_mul,Algebra.smul_def] }
  map_add' x y := by ext φ; simp only [map_add,LinearMap.add_apply]
  map_smul' r x := by ext φ; simp only [map_smul,smul_eq_mul,map_mul,LinearMap.smul_apply,Algebra.smul_def]

/-- Canonical evaluation pairing on the actual coefficient tensor. -/
@[expose] def pairing : S ⊗[R] P →ₗ[S] (Module.Dual R P →ₗ[R] S) :=
  (evaluation R P S).liftBaseChange S

lemma pairing_tmul (s : S) (x : P) (φ : Module.Dual R P) :
    pairing R P S (s ⊗ₜ[R] x) φ=s*algebraMap R S (φ x) := rfl

variable (F : FiniteProjectiveEvaluationFrame318.Frame R P)

@[expose] def reconstruct : (Module.Dual R P →ₗ[R] S) →ₗ[S] S ⊗[R] P where
  toFun φ := ∑ i, φ (F.coordinate i) ⊗ₜ[R] F.vector i
  map_add' φ ψ := by simp only [LinearMap.add_apply,add_tmul,Finset.sum_add_distrib]
  map_smul' s φ := by simp only [LinearMap.smul_apply,smul_eq_mul,← smul_tmul',Finset.smul_sum]

lemma pairing_reconstruct (φ : Module.Dual R P →ₗ[R] S) :
    pairing R P S (reconstruct R P S F φ)=φ := by
  ext λ
  have h := congrArg φ (F.dual_reconstruct λ)
  rw [map_sum] at h
  simp only [map_smul,Algebra.smul_def] at h
  change pairing R P S (∑ i, φ (F.coordinate i) ⊗ₜ[R] F.vector i) λ=φ λ
  rw [map_sum,LinearMap.sum_apply]
  simp only [pairing_tmul]
  simpa only [mul_comm] using h

lemma reconstruct_pairing (z : S ⊗[R] P) :
    reconstruct R P S F (pairing R P S z)=z := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      change (∑ i, s*algebraMap R S (F.coordinate i x) ⊗ₜ[R] F.vector i)=s ⊗ₜ[R] x
      have h := congrArg (fun y => s ⊗ₜ[R] y) (F.reconstruct x)
      simpa only [tmul_sum,tmul_smul,Algebra.smul_def,mul_comm] using h
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Finite PROJECTIVE evaluation duality for arbitrary coefficient rings.
No field, basis of P, or flatness of R→S is assumed. -/
@[expose] def equivalence : S ⊗[R] P ≃ₗ[S] (Module.Dual R P →ₗ[R] S) where
  __ := pairing R P S
  invFun := reconstruct R P S F
  left_inv := reconstruct_pairing R P S F
  right_inv := pairing_reconstruct R P S F
end FiniteProjectiveTensorDual318
