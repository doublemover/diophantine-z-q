module
public import FlatAlgebraEqualizerBaseChange318
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Algebra.Prod
public section
noncomputable section
namespace TensorBinaryAlgebraProducts318
open scoped TensorProduct
universe u
variable {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
  [Algebra R C] [Algebra R D]
variable (A : Type u) [CommRing A] [Algebra R A]
/-- Actual fixed-algebra tensor distribution, including the zero-ring
factors. Native linear distribution is upgraded using pure products. -/
def equivalence : A ⊗[R] (C×D) ≃ₐ[A] (A ⊗[R] C)×(A ⊗[R] D) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (TensorProduct.prodRight R A A C D) (by intros;rfl) (by rfl)
@[simp] lemma tmul (a : A) (z : C×D) :
    equivalence A (a ⊗ₜ[R] z)=(a ⊗ₜ[R] z.1,a ⊗ₜ[R] z.2) := rfl
lemma fst_value (z : A ⊗[R] (C×D)) :
    (equivalence A z).1=TensorAlgebraBaseChange318.map A (AlgHom.fst R C D) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a c => rfl
  | add x y hx hy => simp only [map_add,Prod.fst_add,hx,hy]
lemma snd_value (z : A ⊗[R] (C×D)) :
    (equivalence A z).2=TensorAlgebraBaseChange318.map A (AlgHom.snd R C D) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a c => rfl
  | add x y hx hy => simp only [map_add,Prod.snd_add,hx,hy]
end TensorBinaryAlgebraProducts318
