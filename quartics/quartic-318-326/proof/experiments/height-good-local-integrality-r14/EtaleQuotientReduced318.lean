module
public import EtaleFlatReduced318
public import Mathlib.RingTheory.TensorProduct.Quotient
public section
noncomputable section
namespace EtaleQuotientReduced318
open scoped TensorProduct
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Flat A B] [Algebra.Etale A B]

/-- The actual quotient of the original algebra is reduced whenever the
base quotient is a domain. Its comparison with the etale base change is the
canonical quotient/tensor equivalence, not an assumed geometric identification. -/
theorem reduced (I : Ideal A) [IsDomain (A ⧸ I)] :
    IsReduced (B ⧸ I.map (algebraMap A B)) := by
  letI : IsReduced ((A ⧸ I) ⊗[A] B) :=
    EtaleFlatReduced318.reduced (A ⧸ I) ((A ⧸ I) ⊗[A] B)
  exact isReduced_of_injective
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective

end EtaleQuotientReduced318
