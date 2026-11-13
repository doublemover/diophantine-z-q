module
public import SectionZeroRegularCoordinate318
public import Mathlib.RingTheory.Flat.Basic
public section
noncomputable section
namespace RegularSectionFlatExtension318
open scoped TensorProduct
universe u
variable (A B P Q : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module B Q]

/-- Intrinsic section regularity follows the actual tensor comparison
along a flat scalar extension, without requiring a global rank-one frame. -/
lemma regular [Module.Flat A B] (s : P)
    (hs : SectionZeroRegularCoordinate318.Regular A P s)
    (e : B ⊗[A] P ≃ₗ[B] Q) :
    SectionZeroRegularCoordinate318.Regular B Q (e ((1:B) ⊗ₜ[A] s)) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap (M:=B)
    (SectionZeroRegularCoordinate318.sectionMap A P s) hs
  have unit (b : B) : e (b ⊗ₜ[A] s)=b • e ((1:B) ⊗ₜ[A] s) := by
    simpa only [TensorProduct.smul_tmul',smul_eq_mul,mul_one] using
      e.map_smul b ((1:B) ⊗ₜ[A] s)
  intro a b hab
  change a • e ((1:B) ⊗ₜ[A] s)=b • e ((1:B) ⊗ₜ[A] s) at hab
  have ht : a ⊗ₜ[A] (1:A)=b ⊗ₜ[A] (1:A) := hi (by
    apply e.injective
    simp only [LinearMap.lTensor_tmul]
    change e (a ⊗ₜ[A] ((1:A) • s))=e (b ⊗ₜ[A] ((1:A) • s))
    simpa only [one_smul,unit] using hab)
  have he := congrArg (TensorProduct.rid A B) ht
  simpa only [TensorProduct.rid_tmul,one_smul] using he
end RegularSectionFlatExtension318
