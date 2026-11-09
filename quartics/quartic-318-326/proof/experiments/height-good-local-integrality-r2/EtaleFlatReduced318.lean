module
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace EtaleFlatReduced318
open scoped TensorProduct
variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
  [Algebra A B] [Module.Flat A B] [Algebra.Etale A B]

/-- A flat etale algebra over a domain is reduced: inject the actual algebra
into its fraction-field base change, rather than assume the algebra a domain. -/
theorem reduced : IsReduced B := by
  let K := FractionRing A
  letI : IsReduced (K ⊗[A] B) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[A] B)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective A K))

end EtaleFlatReduced318
