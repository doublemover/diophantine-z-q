module
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace TensorPushoutModule318
open TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (N : Type u) [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The genuine tensor-pushout pairing, preserving the left A action and
sending `(a tensor b, n)` to `a tensor (b smul n)`. -/
@[expose] def pairing : A ⊗[R] B →ₗ[A] N →ₗ[R] A ⊗[R] N :=
  AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun b => (TensorProduct.mk R A N a).comp (Algebra.lsmul R R N b)
          map_add' := by intro b c; ext n; simp [tmul_add]
          map_smul' := by intro r b; ext n; simp }
      map_add' := by intro a c; ext b n; simp
      map_smul' := by intro a c; ext b n; simp [smul_tmul'] }

lemma pairing_tmul (a : A) (b : B) (n : N) :
    pairing R A B N (a ⊗ₜ b) n = a ⊗ₜ (b • n) := rfl

lemma pairing_balanced (b : B) (t : A ⊗[R] B) (n : N) :
    pairing R A B N (b • t) n = pairing R A B N t (b • n) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
      simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, pairing_tmul, mul_smul, smul_comm b c]
  | add t s ht hs => simp [smul_add, map_add, ht, hs]

@[expose] def collapseAdd : (A ⊗[R] B) ⊗[B] N →+ A ⊗[R] N :=
  TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp (pairing R A B N).toAddMonoidHom)
    (pairing_balanced R A B N)

lemma collapseAdd_tmul (t : A ⊗[R] B) (n : N) :
    collapseAdd R A B N (t ⊗ₜ n) = pairing R A B N t n := rfl

/-- Tensoring over the right factor of the actual algebra pushout is
canonically the original scalar extension over R. -/
@[expose] def collapse : (A ⊗[R] B) ⊗[B] N →ₗ[A] A ⊗[R] N :=
  { collapseAdd R A B N with
    map_smul' := by
      intro a t
      induction t using TensorProduct.inductionOn with
      | tmul s n =>
          change pairing R A B N (a • s) n = a • pairing R A B N s n
          exact LinearMap.congr_fun ((pairing R A B N).map_smul a s) n
      | add t s ht hs =>
          change collapseAdd R A B N (a • t) = a • collapseAdd R A B N t at ht
          change collapseAdd R A B N (a • s) = a • collapseAdd R A B N s at hs
          change collapseAdd R A B N (a • (t + s)) = a • collapseAdd R A B N (t + s)
          simp only [smul_add, map_add, ht, hs] }

lemma collapse_tmul (a : A) (b : B) (n : N) :
    collapse R A B N ((a ⊗ₜ[R] b) ⊗ₜ[B] n) = a ⊗ₜ[R] (b • n) := rfl

@[expose] def expand : A ⊗[R] N →ₗ[A] (A ⊗[R] B) ⊗[B] N :=
  AlgebraTensorModule.lift
    { toFun := fun a =>
        ((TensorProduct.mk B (A ⊗[R] B) N) (a ⊗ₜ[R] (1 : B))).restrictScalars R
      map_add' := by intro a c; ext n; simp [add_tmul]
      map_smul' := by intro a c; ext n; rfl }

lemma expand_tmul (a : A) (n : N) :
    expand R A B N (a ⊗ₜ[R] n) = (a ⊗ₜ[R] (1 : B)) ⊗ₜ[B] n := rfl

lemma collapse_expand : (collapse R A B N).comp (expand R A B N) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro a n
  simp [expand_tmul, collapse_tmul]

lemma expand_collapse : (expand R A B N).comp (collapse R A B N) = LinearMap.id := by
  apply LinearMap.toAddMonoidHom_injective
  apply AddMonoidHom.ext
  intro z
  change expand R A B N (collapse R A B N z) = z
  induction z using TensorProduct.inductionOn with
  | tmul t n =>
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
          change (a ⊗ₜ[R] (1 : B)) ⊗ₜ[B] (b • n) = (a ⊗ₜ[R] b) ⊗ₜ[B] n
          rw [← TensorProduct.smul_tmul]
          congr 1
          simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
      | add t s ht hs => simp [add_tmul, map_add, ht, hs]
  | add z w hz hw => simp [map_add, hz, hw]

@[expose] def equivalence : (A ⊗[R] B) ⊗[B] N ≃ₗ[A] A ⊗[R] N :=
  LinearEquiv.ofLinearMap (collapse R A B N) (expand R A B N)
    (collapse_expand R A B N) (expand_collapse R A B N)

lemma equivalence_tmul (a : A) (b : B) (n : N) :
    equivalence R A B N ((a ⊗ₜ[R] b) ⊗ₜ[B] n) = a ⊗ₜ[R] (b • n) := rfl
lemma equivalence_symm_tmul (a : A) (n : N) :
    (equivalence R A B N).symm (a ⊗ₜ[R] n) = (a ⊗ₜ[R] (1 : B)) ⊗ₜ[B] n := rfl
end TensorPushoutModule318
