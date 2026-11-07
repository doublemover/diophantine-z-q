module
public import EtaleNormalization318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace SmoothGenericField318
open scoped TensorProduct nonZeroDivisors
open Algebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R K B:Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDomain B] [Algebra R B]
  [Algebra.Smooth R B] [Module.Finite R B]

abbrev Generic := B⊗[R]K

/-- The actual generic tensor fiber is a domain; this is not a connectedness
claim about an arbitrary possibly disconnected finite cover. -/
theorem generic_domain : IsDomain (Generic (R:=R) (K:=K) (B:=B)) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (Generic (R:=R) (K:=K) (B:=B)) (M:=Algebra.algebraMapSubmonoid B R⁰)
  rintro _ ⟨r,hr,rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  simpa using (FaithfulSMul.algebraMap_injective R B).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem generic_finite : Module.Finite K (Generic (R:=R) (K:=K) (B:=B)) := by
  let e: (K⊗[R]B) ≃ₐ[K] (B⊗[R]K) :=
    { (Algebra.TensorProduct.comm R K B).toRingEquiv with
      commutes' := by intro k; rfl }
  exact Module.Finite.equiv e.toLinearEquiv

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The actual generic fiber is a field, by finite-dimensionality and the
proved domain property. -/
@[expose, instance_reducible] def genericField : Field (Generic (R:=R) (K:=K) (B:=B)) := by
  let:=generic_domain (R:=R) (K:=K) (B:=B)
  let e: (K⊗[R]B) ≃ₐ[K] (B⊗[R]K) :=
    { (Algebra.TensorProduct.comm R K B).toRingEquiv with
      commutes' := by intro k; rfl }
  let : Module.Finite K (B⊗[R]K):=Module.Finite.equiv e.toLinearEquiv
  exact (IsField.of_isDomain_of_finite K (Generic (R:=R) (K:=K) (B:=B))).toField

/-- The actual finite smooth algebra is integrally closed in its generic fiber. -/
theorem generic_integrallyClosedIn :
    IsIntegrallyClosedIn B (Generic (R:=R) (K:=K) (B:=B)) := by
  let:=EtaleNormalization318.smooth_finite_integralClosure (R:=R) (S:=B) (K:=K)
  exact IsIntegrallyClosedIn.of_isIntegralClosure (R:=R)

include R K in
/-- The source open algebra is genuinely normal; no normality premise on B is supplied. -/
theorem smooth_integrallyClosed : IsIntegrallyClosed B := by
  let : Field (Generic (R:=R) (K:=K) (B:=B)):=genericField
  let : IsIntegrallyClosedIn B (Generic (R:=R) (K:=K) (B:=B)):=generic_integrallyClosedIn
  let : FaithfulSMul B (Generic (R:=R) (K:=K) (B:=B)):=
    IsIntegralClosure.faithfulSMul B B (Generic (R:=R) (K:=K) (B:=B))
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn B (Generic (R:=R) (K:=K) (B:=B))

/-- The constructed generic field is the actual fraction field of the open algebra. -/
theorem generic_fractionRing :
    IsFractionRing B (Generic (R:=R) (K:=K) (B:=B)) := by
  let : Field (Generic (R:=R) (K:=K) (B:=B)):=genericField
  have hi:Function.Injective (algebraMap B (Generic (R:=R) (K:=K) (B:=B))):=
    Algebra.TensorProduct.includeLeft_injective (S:=B) (IsFractionRing.injective R K)
  have hM:Algebra.algebraMapSubmonoid B R⁰≤B⁰:=by
    rintro _ ⟨r,hr,rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa using (FaithfulSMul.algebraMap_injective R B).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro b
    exact IsUnit.mk0 _ (by simpa using hi.ne (nonZeroDivisors.coe_ne_zero b))
  · intro x
    obtain ⟨⟨b,m⟩,hm⟩:=IsLocalization.surj (Algebra.algebraMapSubmonoid B R⁰) x
    exact ⟨⟨b,⟨m,hM m.property⟩⟩,hm⟩
  · intro a b hab
    exact ⟨1,by simpa using hi hab⟩

end SmoothGenericField318
