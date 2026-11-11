module
public import UniversallyInjectiveCokernelFlat318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public section
namespace PrincipalQuotientFlatCriterion318
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual equation-multiplication map over the PARAMETER ring. -/
@[expose] def multiply (c : A) : A →ₗ[R] A where
  toFun a := a*c
  map_add' a b := add_mul a b c
  map_smul' r a := smul_mul_assoc r a c

/-- The actual quotient by the original principal equation, not an
abstract cokernel with an unspecified comparison. -/
@[expose] def quotient (c : A) : A →ₗ[R] A ⧸ Ideal.span ({c} : Set A) :=
  (Ideal.Quotient.mkₐ R (Ideal.span ({c} : Set A))).toLinearMap

lemma exact (c : A) : Function.Exact (multiply R A c) (quotient R A c) := by
  rw [LinearMap.exact_iff]
  ext a
  change Ideal.Quotient.mk (Ideal.span ({c} : Set A)) a = 0 ↔
    ∃ b, b*c=a
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']

/-- Quotient flatness follows from ambient flatness and universal
injectivity of THIS equation multiplication. Total-space regularity,
or regularity merely on field fibers, is not substituted for the last
hypothesis. It must be separately produced before applying this result. -/
lemma flat (c : A) [Module.Flat R A]
    (hc : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Injective ((multiply R A c).lTensor N)) :
    Module.Flat R (A ⧸ Ideal.span ({c} : Set A)) :=
  UniversallyInjectiveCokernelFlat318.flat (multiply R A c) (quotient R A c)
    (exact R A c) (Ideal.Quotient.mkₐ_surjective R _) hc
end PrincipalQuotientFlatCriterion318
