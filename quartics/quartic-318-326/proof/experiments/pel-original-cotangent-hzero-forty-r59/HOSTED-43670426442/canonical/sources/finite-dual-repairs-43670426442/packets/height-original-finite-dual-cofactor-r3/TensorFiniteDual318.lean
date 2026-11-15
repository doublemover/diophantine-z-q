module
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Finite
public section
noncomputable section
namespace TensorFiniteDual318
open scoped TensorProduct
variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]
  (e : A ≃ₗ[R] Module.Dual R A) (f : B ≃ₗ[R] Module.Dual R B)

/-- Native tensor distribution identifies the whole finite dual, not only
its values on pure tensors. -/
@[expose] def perfect : A ⊗[R] B ≃ₗ[R] Module.Dual R (A ⊗[R] B) :=
  (TensorProduct.congr e f).trans (TensorProduct.dualDistribEquiv R A B)

theorem perfect_tmul (a a' : A) (b b' : B) :
    perfect R A B e f (a ⊗ₜ[R] b) (a' ⊗ₜ[R] b')=f b b'*e a a' := by
  rw [perfect,LinearEquiv.trans_apply,TensorProduct.congr_tmul,
    TensorProduct.dualDistribEquiv_tmul_tmul]

/-- Multiplicative balance extends across ALL tensor sums by linearity.
This states the actual multiplication/precomposition dual action explicitly. -/
theorem perfect_mul
    (he : ∀ x y z : A,e (x*y) z=e x (y*z))
    (hf : ∀ x y z : B,f (x*y) z=f x (y*z))
    (x y z : A ⊗[R] B) :
    perfect R A B e f (x*y) z=perfect R A B e f x (y*z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul,map_zero,LinearMap.zero_apply]
  | add x x' hx hx' =>
    simp only [add_mul,map_add,LinearMap.add_apply,hx,hx']
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero,zero_mul,map_zero,LinearMap.zero_apply]
    | add y y' hy hy' =>
      simp only [mul_add,add_mul,map_add,LinearMap.add_apply,hy,hy']
    | tmul a' b' =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero,mul_zero]
      | add z z' hz hz' =>
        simp only [mul_add,map_add,hz,hz']
      | tmul a'' b'' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
          perfect_tmul,perfect_tmul,he,hf]
end TensorFiniteDual318
