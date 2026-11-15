module
public import TensorPushoutModule318
public import ScalarExtensionTensor318
public section
noncomputable section
namespace OriginalAlgebraPushoutSections318
open CategoryTheory TensorProduct
open scoped TensorProduct ChangeOfRings
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (A S B O : Type u) [CommRing A] [CommRing S] [CommRing B] [CommRing O]
  [Algebra A S] [Algebra A B] [Algebra S O] [Algebra B O]
  (e : S ⊗[A] B ≃ₐ[S] O)
  (he : ∀ b : B, e ((1 : S) ⊗ₜ[A] b) = algebraMap B O b)
attribute [local instance] Algebra.TensorProduct.rightAlgebra

@[expose] def rightEquivalence : S ⊗[A] B ≃ₗ[B] O where
  __ := e.toAddEquiv
  map_smul' b z := by
    change e (((1 : S) ⊗ₜ[A] b) * z) = algebraMap B O b * e z
    rw [map_mul,he]

variable (N : ModuleCat.{u} B)
local instance : Module A N := Module.compHom N (algebraMap A B)
local instance : IsScalarTower A B N := IsScalarTower.of_compHom ..

@[expose] def transport : (S ⊗[A] B) ⊗[B] N ≃ₗ[S] O ⊗[B] N := by
  let q := TensorProduct.congr (rightEquivalence A S B O e he) (LinearEquiv.refl B N)
  refine { q.toAddEquiv with map_smul' := ?_ }
  intro s z
  induction z using TensorProduct.inductionOn with
  | tmul t n =>
    change e (s • t) ⊗ₜ[B] n = s • (e t ⊗ₜ[B] n)
    rw [e.toLinearEquiv.map_smul,smul_tmul']
  | add x y hx hy =>
    change q (s • x) = s • q x at hx
    change q (s • y) = s • q y at hy
    change q (s • (x+y)) = s • q (x+y)
    simp only [smul_add,map_add,hx,hy]

/-- The actual full chart-ring extension IS the smaller polynomial/Laurent
extension after the original ring pushout; no basis is chosen. -/
@[expose] def tensorEquivalence : S ⊗[A] N ≃ₗ[S] O ⊗[B] N :=
  (TensorPushoutModule318.equivalence A S B N).symm.trans (transport A S B O e he N)

lemma tensorEquivalence_tmul (s : S) (n : N) :
    tensorEquivalence A S B O e he N (s ⊗ₜ[A] n) = (algebraMap S O s) ⊗ₜ[B] n := by
  change e (s ⊗ₜ[A] (1 : B)) ⊗ₜ[B] n = _
  exact congrArg (fun o => o ⊗ₜ[B] n) (e.commutes s)

variable (M : ModuleCat.{u} O)
local instance : Module S M := Module.compHom M (algebraMap S O)
local instance : IsScalarTower S O M := IsScalarTower.of_compHom ..
local instance : Module S ((ModuleCat.extendScalars (algebraMap B O)).obj N) :=
  Module.compHom _ (algebraMap S O)
local instance : IsScalarTower S O ((ModuleCat.extendScalars (algebraMap B O)).obj N) :=
  IsScalarTower.of_compHom ..

/-- Retains the specified genuine affine section comparison. The map on
one tensor x is exactly its original categorical extension unit. -/
@[expose] def sections (c : (ModuleCat.extendScalars (algebraMap B O)).obj N ≅ M) :
    S ⊗[A] N ≃ₗ[S] M :=
  (tensorEquivalence A S B O e he N).trans
    (((ScalarExtensionTensor318.tensorEquiv (S := B) (T := O) N).symm.restrictScalars S).trans
      (c.toLinearEquiv.restrictScalars S))

lemma sections_unit (c : (ModuleCat.extendScalars (algebraMap B O)).obj N ≅ M) (n : N) :
    sections A S B O e he N M c ((1 : S) ⊗ₜ[A] n) =
      c.hom ((ModuleCat.extendRestrictScalarsAdj (algebraMap B O)).unit.app N n) := by
  change c.toLinearEquiv ((ScalarExtensionTensor318.tensorEquiv (S := B) (T := O) N).symm
    (tensorEquivalence A S B O e he N ((1 : S) ⊗ₜ[A] n))) = _
  rw [tensorEquivalence_tmul,map_one]
  rfl
end OriginalAlgebraPushoutSections318
