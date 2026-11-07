module
public import JModelFunctionField318
public import SmoothGenericField318
public section
noncomputable section
namespace JModelGenericTensor318
open Algebra
open scoped TensorProduct nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

abbrev Generic := B⊗[OpenJModel318.Base N] FractionRing (OpenJModel318.Base N)

/-- The actual generic tensor fiber is the fraction ring of B. -/
theorem generic_fractionRing (hN:N≠0) : IsFractionRing B (Generic N B) := by
  have hd:=OpenJNormalModel318.denominator_ne_zero N hN
  letI:IsDomain (OpenJModel318.Base N):=IsLocalization.Away.isDomain _ hd
  letI:IsIntegrallyClosed (OpenJModel318.Base N):=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (OpenJModel318.denominator N))
      (by rintro x ⟨n,rfl⟩;exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd))
  exact SmoothGenericField318.generic_fractionRing
    (R:=OpenJModel318.Base N) (K:=FractionRing (OpenJModel318.Base N)) (B:=B)

attribute [local instance] JModelFunctionField318.sourceAlgebra

/-- The actual proper model function field is canonically the actual generic
finite-cover tensor algebra, with original B coefficients preserved. -/
@[expose] def genericEquiv (hN:N≠0) :
    (OpenJProjectiveMap318.coverMap N B).normalization.functionField ≃ₐ[B] Generic N B := by
  letI:=generic_fractionRing N B hN
  letI:=JModelFunctionField318.functionField_fractionRing N B
  exact IsLocalization.algEquiv B⁰ _ _

theorem genericEquiv_coeff (hN:N≠0) (b:B) :
    genericEquiv N B hN (algebraMap B _ b)=algebraMap B (Generic N B) b :=
  (genericEquiv N B hN).commutes b
end JModelGenericTensor318
