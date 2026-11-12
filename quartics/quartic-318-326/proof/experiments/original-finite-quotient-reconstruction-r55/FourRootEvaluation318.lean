module
public import FourRootAutomorphisms318
public import SourceTwistArithmetic318
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public section
noncomputable section
open scoped BigOperators
namespace FourRootEvaluation318
open scoped TensorProduct
open QuadraticPresentation318 KummerTensorField318 FourRootAutomorphisms318
variable {F L : Type*} [Field F] [CharZero F] [CommRing L] [Algebra F L]
variable (a : Fin 4 → F) (x : Fin 4 → L)
  (hx : ∀ i, x i ^ 2 = algebraMap F L (a i))

@[expose] def rootHom (i : Fin 4) : RootRing (a i) →ₐ[F] L :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F L) (x i) (by
    change Polynomial.aeval (x i) (Polynomial.X ^ 2 - Polynomial.C (a i)) = 0
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hx, sub_self])

@[simp] theorem rootHom_root (i : Fin 4) :
    rootHom a x hx i (AdjoinRoot.root (polynomial (a i))) = x i :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The homomorphism is evaluated on the original four polynomial quotients. -/
@[expose] def evaluate : Raw a →ₐ[F] L :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (rootHom a x hx 0) (rootHom a x hx 1)
      (fun _ _ => Commute.all _ _))
    (Algebra.TensorProduct.lift (rootHom a x hx 2) (rootHom a x hx 3)
      (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

@[simp] theorem evaluate_generator (i : Fin 4) :
    evaluate a x hx (generator a i) = x i := by
  fin_cases i <;> simp [generator, evaluate, Algebra.TensorProduct.lift_tmul]

/-- Literal complementary root product on the original tensor ring. This
uses only its original multiplication, without assuming a field instance. -/
@[expose] def characterGenerator (i : Fin 4) : Raw a :=
  ∏ j : Fin 3, generator a (SourceTwistArithmetic318.complement i j)

/-- Equality is checked on the actual four root generators, not on a replacement basis. -/
theorem hom_ext {f g : Raw a →ₐ[F] L}
    (h : ∀ i, f (generator a i) = g (generator a i)) : f = g := by
  apply Algebra.TensorProduct.ext
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 0
    · apply AdjoinRoot.algHom_ext
      exact h 1
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 2
    · apply AdjoinRoot.algHom_ext
      exact h 3

/-- A supplied action is intertwined only after its four actual root formulas are proved. -/
theorem equivariant (e : L ≃ₐ[F] L) (s : Fin 4 → Bool)
    (he : ∀ i, e (x i) = if s i then -x i else x i) (z : Raw a) :
    e (evaluate a x hx z) = evaluate a x hx (signEquiv a s z) := by
  have h : e.toAlgHom.comp (evaluate a x hx) =
      (evaluate a x hx).comp (signEquiv a s).toAlgHom := by
    apply hom_ext
    intro i
    change e (evaluate a x hx (generator a i)) =
      evaluate a x hx (signEquiv a s (generator a i))
    rw [evaluate_generator, he, signEquiv_generator]
    split <;> simp_all
  exact congrArg (fun f : Raw a →ₐ[F] L => f z) h

end FourRootEvaluation318
