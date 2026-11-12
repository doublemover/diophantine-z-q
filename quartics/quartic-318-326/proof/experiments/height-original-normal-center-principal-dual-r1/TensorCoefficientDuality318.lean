module
public import PerfectCoefficientPairing318
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace TensorCoefficientDuality318
open Module
open scoped TensorProduct
set_option maxHeartbeats 1800000

/-- Concrete finite integral multiplication pairing data. The defining
identity supplies a literal dual basis over an arbitrary commutative base. -/
structure Frame (R A ι : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Fintype ι] [DecidableEq ι] where
  basis : Basis ι R A
  switch : ι → ι
  involutive : Function.Involutive switch
  coefficient : A →ₗ[R] R
  pairing : ∀ i j,coefficient (basis i*basis j)=if j=switch i then 1 else 0

namespace Frame
variable {R A B ι κ : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (F : Frame R A ι) (G : Frame R B κ)
@[expose] def duality : A ≃ₗ[R] Module.Dual R A :=
  PerfectCoefficientPairing318.equivalence F.basis F.switch F.involutive F.coefficient F.pairing

theorem duality_apply (x y : A) : F.duality x y=F.coefficient (x*y) := rfl

theorem duality_mul (a x y : A) : F.duality (a*x) y=F.duality x (a*y) :=
  PerfectCoefficientPairing318.multiplication_compatibility F.basis F.switch F.involutive
    F.coefficient F.pairing a x y

@[expose] def tensorCoefficient : A ⊗[R] B →ₗ[R] R := TensorProduct.lift
  { toFun := fun a => F.coefficient a • G.coefficient
    map_add' := fun a b => by rw [map_add,add_smul]
    map_smul' := fun r a => by rw [map_smul,smul_smul] }

theorem tensorCoefficient_tmul (a : A) (b : B) :
    tensorCoefficient F G (a ⊗ₜ[R] b)=F.coefficient a*G.coefficient b := by
  rw [tensorCoefficient,TensorProduct.lift.tmul]
  rfl

@[expose] def tensor : Frame R (A ⊗[R] B) (ι × κ) where
  basis := F.basis.tensorProduct G.basis
  switch := fun i => (F.switch i.1,G.switch i.2)
  involutive i := by rcases i with ⟨i,j⟩; simp only [F.involutive i,G.involutive j]
  coefficient := tensorCoefficient F G
  pairing := by
    rintro ⟨i,j⟩ ⟨k,l⟩
    rw [Basis.tensorProduct_apply,Basis.tensorProduct_apply,Algebra.TensorProduct.tmul_mul_tmul,
      tensorCoefficient_tmul,F.pairing,G.pairing]
    by_cases hk : k=F.switch i <;> by_cases hl : l=G.switch j <;> simp [hk,hl]

/-- The actual tensor ring multiplication pairing is perfect integrally;
no separability, root invertibility or discriminant localization premise. -/
theorem tensor_duality_apply (x y : A ⊗[R] B) :
    (F.tensor G).duality x y=tensorCoefficient F G (x*y) := rfl
end Frame
end TensorCoefficientDuality318
