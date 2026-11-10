module
public import ScalarExtensionQuotient318
public section
noncomputable section
namespace EndomorphismCokernelBaseChange318
open TensorProduct
open scoped TensorProduct
universe u v w z
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {B : Type w} [AddCommGroup B] [Module R B]
  {B' : Type z} [AddCommGroup B'] [Module S B']
  (t : B →ₗ[R] B) (t' : B' →ₗ[S] B') (e : S ⊗[R] B ≃ₗ[S] B')
  (h : e.toLinearMap.comp (t.baseChange S)=t'.comp e.toLinearMap)

include h in
lemma image : (ScalarExtensionQuotient318.image S t.range).map e.toLinearMap=t'.range := by
  rw [ScalarExtensionQuotient318.image_range,← LinearMap.range_comp,h]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.surjective)

/-- Base change of the ACTUAL coordinate-power quotient, using right
exactness and the specified original section map. No flatness hypothesis. -/
@[expose] def equivalence : S ⊗[R] (B ⧸ t.range) ≃ₗ[S] B' ⧸ t'.range :=
  (ScalarExtensionQuotient318.equivalence S t.range).symm.trans
    (Submodule.Quotient.equiv _ _ e (image S t t' e h))

lemma pure_tensor (s : S) (x : B) :
    equivalence S t t' e h (s ⊗ₜ[R] t.range.mkQ x)=t'.range.mkQ (e (s ⊗ₜ[R] x)) := by
  change Submodule.Quotient.equiv _ _ e _
    ((ScalarExtensionQuotient318.equivalence S t.range).symm (s ⊗ₜ[R] t.range.mkQ x))=_
  rw [← ScalarExtensionQuotient318.equivalence_mk S t.range,LinearEquiv.symm_apply_apply]
  rfl
end EndomorphismCokernelBaseChange318
