module
public import FlatQuotientIdealTensor318
public section
noncomputable section
namespace FlatPrincipalCoefficientRegular318
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] (c : A)
  [Module.Flat R (A ⧸ Ideal.span ({c} : Set A))]
  (hc : ∀ a : A,a*c=0 → a=0)
lemma multiply_injective : Function.Injective (PrincipalQuotientFlatCriterion318.multiply R A c) := by
  intro a b h
  apply sub_eq_zero.mp
  apply hc
  rw [sub_mul]
  exact sub_eq_zero.mpr h
lemma tensor_injective : Function.Injective ((PrincipalQuotientFlatCriterion318.multiply R A c).lTensor S) :=
  LinearMap.lTensor_injective_of_exact_of_flat (PrincipalQuotientFlatCriterion318.quotient R A c)
    (Ideal.Quotient.mkₐ_surjective R _) (PrincipalQuotientFlatCriterion318.multiply R A c)
    (multiply_injective R A c hc) (PrincipalQuotientFlatCriterion318.exact R A c) S
lemma tensor_multiply (z : S ⊗[R] A) :
    (PrincipalQuotientFlatCriterion318.multiply R A c).lTensor S z=z*((1 : S) ⊗ₜ[R] c) := by
  induction z using TensorProduct.inductionOn with
  | tmul s a => simp only [LinearMap.lTensor_tmul,PrincipalQuotientFlatCriterion318.multiply,
      Algebra.TensorProduct.tmul_mul_tmul,mul_one]
  | add x y hx hy => simp only [map_add,hx,hy,add_mul]
/-- A flat principal closed family remains a genuine nonzerodivisor
quotient after EVERY coefficient change, including nonflat nilpotent tests. -/
lemma regular : ∀ z : S ⊗[R] A,z*((1 : S) ⊗ₜ[R] c)=0 → z=0 := by
  intro z hz
  apply tensor_injective R A S c hc
  rw [map_zero,tensor_multiply,hz]
lemma ideal : FlatQuotientIdealTensor318.extended R A S (Ideal.span ({c} : Set A))=
    Ideal.span ({(1 : S) ⊗ₜ[R] c} : Set (S ⊗[R] A)) := by
  rw [FlatQuotientIdealTensor318.extended,Ideal.map_span,Set.image_singleton]
  rfl
/-- Actual rank-one ideal frame after arbitrary coefficient change,
with multiplication by the same transported equation as its inclusion. -/
@[expose] def frame : (S ⊗[R] A) ≃ₗ[S ⊗[R] A]
    Ideal.span ({(1 : S) ⊗ₜ[R] c} : Set (S ⊗[R] A)) :=
  RegularPrincipalIdealFrame318.equivalence _ _ (regular R A S c hc)
lemma frame_value (z : S ⊗[R] A) : (frame R A S c hc z).val=z*((1 : S) ⊗ₜ[R] c) := rfl
end FlatPrincipalCoefficientRegular318
