module

public import FaithfullyFlatTorsor318
public import Mathlib.RingTheory.IsTensorProduct

@[expose] public section

noncomputable section

open TensorProduct

namespace TensorTower318

variable (R A B S : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra R S]

/-- The actual scalar extension of the given intermediate-algebra inclusion. -/
def extensionMap : A ⊗[R] S →ₐ[R] B ⊗[R] S :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A B) (AlgHom.id R S)

instance extensionAlgebra : Algebra (A ⊗[R] S) (B ⊗[R] S) :=
  (extensionMap R A B S).toRingHom.toAlgebra

@[simp] theorem extensionMap_tmul (a : A) (s : S) :
    algebraMap (A ⊗[R] S) (B ⊗[R] S) (a ⊗ₜ[R] s) =
      algebraMap A B a ⊗ₜ[R] s := rfl

instance towerA : IsScalarTower A (A ⊗[R] S) (B ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq' (by ext a; simp [Algebra.TensorProduct.algebraMap_apply])

instance towerR : IsScalarTower R (A ⊗[R] S) (B ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R A B])

attribute [local instance] Algebra.TensorProduct.rightAlgebra

instance towerS : IsScalarTower S (A ⊗[R] S) (B ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext s
    change 1 ⊗ₜ[R] s = algebraMap (A ⊗[R] S) (B ⊗[R] S) (1 ⊗ₜ[R] s)
    simp)

/-- The actual tensor square of the original algebra tower is a pushout. -/
instance pushout : Algebra.IsPushout A B (A ⊗[R] S) (B ⊗[R] S) :=
  Algebra.IsPushout.tensorProduct_tensorProduct R S A B (by
    ext s
    change algebraMap (A ⊗[R] S) (B ⊗[R] S) (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
    simp)

/-- The actual intermediate-base extension, with the correct invariant base. -/
def baseEquiv : (A ⊗[R] S) ⊗[A] B ≃ₐ[A ⊗[R] S] (B ⊗[R] S) := by
  letI := (pushout R A B S).symm
  exact Algebra.IsPushout.equiv A (A ⊗[R] S) B (B ⊗[R] S)

@[simp] theorem baseEquiv_tmul (a : A) (s : S) (b : B) :
    baseEquiv R A B S ((a ⊗ₜ[R] s) ⊗ₜ[A] b) =
      (algebraMap A B a * b) ⊗ₜ[R] s := by
  rw [baseEquiv, Algebra.IsPushout.equiv_tmul, extensionMap_tmul]
  change (algebraMap A B a ⊗ₜ[R] s) * (b ⊗ₜ[R] 1) = _
  simp

end TensorTower318
