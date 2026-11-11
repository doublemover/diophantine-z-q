module
public import OriginalTensorTraceBaseChange318
public import Mathlib.RingTheory.Norm.Basic
public section
noncomputable section
namespace OriginalRightTensorNormTrace318
open scoped TensorProduct
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
@[expose] def commute : A ⊗[R] S ≃ₐ[A] S ⊗[R] A := Algebra.TensorProduct.commRight R A S
lemma algebraMap_right (a : A) : algebraMap A (S ⊗[R] A) a = 1 ⊗ₜ[R] a := rfl
variable [Module.Free R S] [Module.Finite R S]
lemma norm_coefficient (s : S) : Algebra.norm A (s ⊗ₜ[R] 1 : S ⊗[R] A) =
    algebraMap R A (Algebra.norm R s) := by
  change Algebra.norm A (commute R S A (1 ⊗ₜ[R] s)) = _
  rw [Algebra.norm_eq_of_algEquiv, OriginalTensorTraceBaseChange318.norm]
/-- This is the actual tensor orientation used by the original affine
fiber-product model: S tensor the test ring, with the test ring acting on RIGHT. -/
lemma norm_infinitesimal (e : A) (he : e * e = 0) (s : S) :
    Units.map (Algebra.norm A)
      (InfinitesimalUnitCocycle318.infinitesimal
        (algebraMap A (S ⊗[R] A) e)
        (by rw [← map_mul, he, map_zero]) (s ⊗ₜ[R] 1)) =
    InfinitesimalUnitCocycle318.infinitesimal e he (algebraMap R A (Algebra.trace R S s)) := by
  apply Units.ext
  have h := congrArg Units.val (OriginalTensorTraceBaseChange318.norm_infinitesimal R S A e he s)
  change Algebra.norm A (1 + algebraMap A (A ⊗[R] S) e * (1 ⊗ₜ[R] s)) =
    1 + e * algebraMap R A (Algebra.trace R S s) at h
  calc
    Algebra.norm A (1 + algebraMap A (S ⊗[R] A) e * (s ⊗ₜ[R] 1)) =
        Algebra.norm A (commute R S A (1 + algebraMap A (A ⊗[R] S) e * (1 ⊗ₜ[R] s))) := by
      congr 1
      simp only [map_add, map_one, map_mul, AlgEquiv.commutes, commute,
        Algebra.TensorProduct.commRight_tmul]
    _ = Algebra.norm A (1 + algebraMap A (A ⊗[R] S) e * (1 ⊗ₜ[R] s)) :=
      Algebra.norm_eq_of_algEquiv (commute R S A) _
    _ = _ := h
end OriginalRightTensorNormTrace318
