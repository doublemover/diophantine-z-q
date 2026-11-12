module
public import PELOriginalCM210IntegralTraceMatrix318
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public section
noncomputable section
namespace PELOriginalCM210NativeDiscriminant318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210IntegralTraceMatrix318
@[expose] def integerAlgEquiv : R≃ₐ[ℤ]O where
  __ := integerEquiv
  commutes' n := map_intCast integerEquiv n
@[expose] def nativeBasis : Module.Basis (Fin 2) ℤ O :=
  integralBasis.map integerAlgEquiv.toLinearEquiv
lemma native_discriminant : NumberField.discr K=(-840:ℤ) := by
  calc
    NumberField.discr K=Algebra.discr ℤ nativeBasis :=
      (NumberField.discr_eq_discr K nativeBasis).symm
    _=Algebra.discr ℤ integralBasis := by
      change Algebra.discr ℤ (integerAlgEquiv ∘ integralBasis)=Algebra.discr ℤ integralBasis
      exact (Algebra.discr_eq_discr_of_algEquiv integralBasis integerAlgEquiv).symm
    _=(-840:ℤ) := basis_discriminant
lemma native_abs_discriminant : (NumberField.discr K).natAbs=840 := by
  rw [native_discriminant]; norm_num

end PELOriginalCM210NativeDiscriminant318
