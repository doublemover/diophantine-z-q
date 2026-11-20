module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public section

noncomputable section

namespace OriginalRationalizedFreeRankOne318

open scoped TensorProduct

variable {R F M : Type*} [CommRing R] [Field F] [Algebra R F]
  [AddCommGroup M] [Module R M]

/-- Extend the actual free line over R to F, retaining the F-linear
module structure rather than only restricting scalars back to R. -/
def extendLine (e : M ≃ₗ[R] R) : F ⊗[R] M ≃ₗ[F] F :=
  (LinearEquiv.baseChange R F M R e).trans
    (TensorProduct.AlgebraTensorModule.rid R F F)

theorem finite_and_one (e : M ≃ₗ[R] R) :
    FiniteDimensional F (F ⊗[R] M) ∧ Module.finrank F (F ⊗[R] M)=1 :=
  ⟨(extendLine e).symm.finiteDimensional,
    (extendLine e).finrank_eq.trans (Module.finrank_self F)⟩

end OriginalRationalizedFreeRankOne318

#print axioms OriginalRationalizedFreeRankOne318.finite_and_one
