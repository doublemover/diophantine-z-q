module
public import SymmetricScalarChange318
public import SymmetricPrimitiveRegular318
public section
noncomputable section
namespace SymmetricScalarRegular318
open scoped TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  (M : Type w) [AddCommGroup M] [Module R M]
  (v : B ⊗[R] M) (φ : (B ⊗[R] M) →ₗ[B] B) (hv : φ v=1)

/-- Regularity transported by the CANONICAL symmetric scalar-change
isomorphism, with the actual primitive vector and splitting retained. -/
theorem regular (a : B ⊗[R] SymmetricAlgebra R M)
    (ha : a * (SymmetricScalarChange318.equivalence R B M).symm
      (SymmetricAlgebra.ι B (B ⊗[R] M) v)=0) : a=0 := by
  have he := congrArg (SymmetricScalarChange318.equivalence R B M) ha
  rw [map_mul,AlgEquiv.apply_symm_apply,map_zero] at he
  have hz := SymmetricPrimitiveRegular318.generator_regular B (B ⊗[R] M) φ v hv
    ((SymmetricScalarChange318.equivalence R B M) a) he
  apply (SymmetricScalarChange318.equivalence R B M).injective
  simpa only [map_zero] using hz
end SymmetricScalarRegular318
