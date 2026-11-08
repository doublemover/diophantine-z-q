module
public import EtaleNormalization318
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace EtaleDomainNormal318
open scoped TensorProduct nonZeroDivisors
open Algebra
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R K B:Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDomain B] [Algebra R B] [Algebra.Etale R B]
abbrev Generic := B ⊗[R] K

lemma generic_domain : IsDomain (Generic (R:=R) (K:=K) (B:=B)) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (Generic (R:=R) (K:=K) (B:=B)) (M:=Algebra.algebraMapSubmonoid B R⁰)
  rintro _ ⟨r,hr,rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  simpa using (FaithfulSMul.algebraMap_injective R B).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma generic_finite : Module.Finite K (Generic (R:=R) (K:=K) (B:=B)) := by
  letI:Module.Finite K (K ⊗[R] B):=Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] B)
  let e:(K ⊗[R] B) ≃ₐ[K] (B ⊗[R] K):=
    { (Algebra.TensorProduct.comm R K B).toRingEquiv with
      commutes':=by intro k; rfl }
  exact Module.Finite.equiv e.toLinearEquiv

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[expose, instance_reducible] def genericField : Field (Generic (R:=R) (K:=K) (B:=B)) := by
  letI:=generic_domain (R:=R) (K:=K) (B:=B)
  letI:=generic_finite (R:=R) (K:=K) (B:=B)
  exact (IsField.of_isDomain_of_finite K (Generic (R:=R) (K:=K) (B:=B))).toField

/-- Smooth integral-closure base change supplies integral closedness in the
actual generic algebra without requiring the original etale algebra finite. -/
lemma generic_integrallyClosedIn : IsIntegrallyClosedIn B (Generic (R:=R) (K:=K) (B:=B)) := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨Algebra.TensorProduct.includeLeft_injective (S:=B) (IsFractionRing.injective R K),?_⟩
  intro x hx
  obtain ⟨t,ht⟩:=(TensorProduct.toIntegralClosure_bijective_of_smooth
    (R:=R) (S:=B) (B:=K)).surjective ⟨x,hx⟩
  obtain ⟨b,hb⟩:=EtaleNormalization318.comparison_image (R:=R) (S:=B) (K:=K) t
  exact ⟨b,hb.trans (congrArg Subtype.val ht)⟩

include R K in
/-- An etale domain over a normal domain is normal. No finiteness of the
original algebra as a module is assumed; only its generic fiber is finite. -/
theorem integrallyClosed : IsIntegrallyClosed B := by
  letI:Field (Generic (R:=R) (K:=K) (B:=B)):=genericField
  letI:IsIntegrallyClosedIn B (Generic (R:=R) (K:=K) (B:=B)):=generic_integrallyClosedIn
  letI:FaithfulSMul B (Generic (R:=R) (K:=K) (B:=B)):=
    IsIntegralClosure.faithfulSMul B B (Generic (R:=R) (K:=K) (B:=B))
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn B (Generic (R:=R) (K:=K) (B:=B))
end EtaleDomainNormal318
