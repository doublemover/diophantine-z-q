module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Tactic
public section
noncomputable section
namespace TensorFractionField318
open scoped TensorProduct nonZeroDivisors
set_option maxHeartbeats 700000
variable {R K A F:Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Algebra R A] [Module.Free R A]
  [Field F] [Algebra A F]

/-- If the actual generic tensor algebra is a field, it is the fraction
field of the whole torsion-free order, with its specified embedding. -/
theorem fractionRing (e:A⊗[R]K≃ₐ[A]F) : IsFractionRing A F := by
  letI:IsLocalization (Algebra.algebraMapSubmonoid A R⁰) F:=
    IsLocalization.isLocalization_of_algEquiv _ e
  have hi:Function.Injective (algebraMap A F) := by
    intro x y h
    apply Algebra.TensorProduct.includeLeft_injective (S:=A) (IsFractionRing.injective R K)
    apply e.injective
    change e (algebraMap A (A⊗[R]K) x)=e (algebraMap A (A⊗[R]K) y)
    simpa only [AlgEquiv.commutes] using h
  have hM:Algebra.algebraMapSubmonoid A R⁰≤A⁰ := by
    rintro _ ⟨r,hr,rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R A).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  refine { map_units:=?_,surj:=?_,exists_of_eq:=?_ }
  · intro a
    exact IsUnit.mk0 _ (by simpa only [map_zero] using hi.ne (nonZeroDivisors.coe_ne_zero a))
  · intro x
    obtain ⟨⟨a,m⟩,hm⟩:=IsLocalization.surj (Algebra.algebraMapSubmonoid A R⁰) x
    exact ⟨⟨a,⟨m,hM m.property⟩⟩,hm⟩
  · intro x y h
    exact ⟨1,by simpa using hi h⟩
end TensorFractionField318
