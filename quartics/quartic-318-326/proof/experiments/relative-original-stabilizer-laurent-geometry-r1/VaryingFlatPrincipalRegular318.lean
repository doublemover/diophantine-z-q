module
public import VaryingFlatIdealCoefficient318
public section
noncomputable section
namespace VaryingFlatPrincipalRegular318
open scoped TensorProduct
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (c : S ⊗[R] A) [hflat : Module.Flat S ((S ⊗[R] A) ⧸ Ideal.span ({c} : Set (S ⊗[R] A)))]
  (hc : ∀ z : S ⊗[R] A,z*c=0 → z=0)
local notation "f" => VaryingWholeQuotientTensor318.source R A S T
local notation "e" => VaryingSourceTensorCollapse318.equivalence R A S T
include hc hflat in
/-- Nonzerodivisor equations of the actual original flat quotient
persist after every original coefficient map, without flatness of T/S. -/
lemma regular : ∀ z : T ⊗[R] A,z*f c=0 → z=0 := by
  intro z hz
  have hreg := FlatPrincipalCoefficientRegular318.regular S (S ⊗[R] A) T c hc
  have he : e.symm z*((1 : T) ⊗ₜ[S] c)=0 := by
    apply e.injective
    rw [map_mul,map_zero,VaryingSourceTensorCollapse318.source,e.apply_symm_apply]
    exact hz
  have h := hreg (e.symm z) he
  exact e.symm.injective (h.trans (map_zero e.symm).symm)
lemma ideal : VaryingWholeQuotientTensor318.ideal R A S T (Ideal.span ({c} : Set (S ⊗[R] A)))=
    Ideal.span ({f c} : Set (T ⊗[R] A)) := by
  rw [VaryingWholeQuotientTensor318.ideal,Ideal.map_span,Set.image_singleton]
@[expose] def frame : (T ⊗[R] A) ≃ₗ[T ⊗[R] A] Ideal.span ({f c} : Set (T ⊗[R] A)) :=
  RegularPrincipalIdealFrame318.equivalence _ _ (regular R A S T c hc)
lemma frame_value (z : T ⊗[R] A) : (frame R A S T c hc z).val=z*f c := rfl
end VaryingFlatPrincipalRegular318
