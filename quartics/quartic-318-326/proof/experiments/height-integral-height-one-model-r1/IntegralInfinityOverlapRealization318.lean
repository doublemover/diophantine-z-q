module
public import IntegralInfinityBaseEquiv318
public section
noncomputable section
namespace IntegralInfinityOverlapRealization318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section Generic
variable (A S B : Type*) [CommRing A] [CommRing S] [CommRing B] [Algebra A S] [Algebra A B]
/-- The actual right-inclusion algebra used to view scalar extension as a
localization of the original order. -/
@[expose] def rightAlgebra : Algebra B (S ⊗[A] B) :=
  (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom.toAlgebra

/-- A scalar-base principal localization is the actual principal localization
of the order after tensor extension, along the specified inclusion. -/
theorem baseChange_localization (x : A) [IsLocalization.Away x S] :
    letI := rightAlgebra A S B
    IsLocalization.Away (algebraMap A B x) (S ⊗[A] B) := by
  letI := rightAlgebra A S B
  letI : IsLocalization.Away (algebraMap A B x) (B ⊗[A] S) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers x)) (B ⊗[A] S))
  let e : B ⊗[A] S ≃ₐ[B] S ⊗[A] B :=
    { (Algebra.TensorProduct.comm A B S).toRingEquiv with commutes' := by intro b;rfl }
  exact IsLocalization.isLocalization_of_algEquiv
    (S := B ⊗[A] S) (Submonoid.powers (algebraMap A B x)) e
end Generic

open IntegralSourceBranches318 IntegralInfinityCommonBase318 IntegralInfinityCommonOrder318
open IntegralInfinityBaseEquiv318
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

theorem finiteOrder_localization :
    letI := rightAlgebra (OpenBase R c 0) (CommonBase R c) (OpenOrder R c 0)
    IsLocalization.Away (algebraMap (OpenBase R c 0) (OpenOrder R c 0) (rootOpen R c))
      (CommonBase R c ⊗[OpenBase R c 0] OpenOrder R c 0) :=
  baseChange_localization (OpenBase R c 0) (CommonBase R c) (OpenOrder R c 0) (rootOpen R c)

theorem infinityOrder_localization :
    letI := rightAlgebra (IntegralInfinityChart318.Base R c) (CommonBase R c)
      (IntegralInfinityChart318.Order R c)
    IsLocalization.Away (IntegralInfinityChart318.coordinate R c)
      (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c) := by
  letI := common_isInfinityLocalization R c
  exact baseChange_localization (IntegralInfinityChart318.Base R c) (CommonBase R c)
    (IntegralInfinityChart318.Order R c)
    (algebraMap R[X] (IntegralInfinityChart318.Base R c) Polynomial.X)

/-- The overlap equivalence simultaneously relates the actual finite and
infinity order localizations, with their common coefficient-base structure.
The preceding two theorems establish that these tensors are the genuine
principal opens, not merely base changes to an unrelated common algebra. -/
@[expose] def actualOverlapEquiv :
    CommonBase R c ⊗[OpenBase R c 0] OpenOrder R c 0 ≃ₐ[CommonBase R c]
      CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c :=
  commonOrderEquiv R c

end IntegralInfinityOverlapRealization318
