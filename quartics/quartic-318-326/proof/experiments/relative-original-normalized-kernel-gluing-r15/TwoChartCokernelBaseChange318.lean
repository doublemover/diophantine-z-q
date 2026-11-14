module
public import ScalarExtensionQuotient318
public section
noncomputable section
namespace TwoChartCokernelBaseChange318
open TensorProduct
universe u v
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {A B M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
  [Module R A] [Module R B] [Module R M]
  {A' B' M' : Type*} [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup M']
  [Module S A'] [Module S B'] [Module S M']
  (f : A →ₗ[R] M) (g : B →ₗ[R] M) (f' : A' →ₗ[S] M') (g' : B' →ₗ[S] M')
  (eA : S ⊗[R] A ≃ₗ[S] A') (eB : S ⊗[R] B ≃ₗ[S] B')
  (eM : S ⊗[R] M ≃ₗ[S] M')
  (hf : eM.toLinearMap.comp (f.baseChange S) = f'.comp eA.toLinearMap)
  (hg : eM.toLinearMap.comp (g.baseChange S) = g'.comp eB.toLinearMap)

include hf in
lemma left_image : (ScalarExtensionQuotient318.image S f.range).map eM.toLinearMap = f'.range := by
  rw [ScalarExtensionQuotient318.image_range,← LinearMap.range_comp,hf]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr eA.surjective)

include hg in
lemma right_image : (ScalarExtensionQuotient318.image S g.range).map eM.toLinearMap = g'.range := by
  rw [ScalarExtensionQuotient318.image_range,← LinearMap.range_comp,hg]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr eB.surjective)

/-- Right exactness yields the original two-image quotient base-change
isomorphism once the ACTUAL three chart comparisons and both restriction
squares have been supplied. No H0/kernel base-change claim is made. -/
@[expose] def equivalence : S ⊗[R] (M ⧸ (f.range ⊔ g.range)) ≃ₗ[S]
    M' ⧸ (f'.range ⊔ g'.range) :=
  (ScalarExtensionQuotient318.twoImageEquivalence S f.range g.range).trans
    (Submodule.Quotient.equiv _ _ eM (by
      rw [Submodule.map_sup,left_image S f f' eA eM hf,right_image S g g' eB eM hg]))

lemma equivalence_tmul (s : S) (m : M) :
    equivalence S f g f' g' eA eB eM hf hg
      (s ⊗ₜ[R] (f.range ⊔ g.range).mkQ m) =
        (f'.range ⊔ g'.range).mkQ (eM (s ⊗ₜ[R] m)) := by
  change Submodule.Quotient.equiv _ _ eM _
    (ScalarExtensionQuotient318.twoImageEquivalence S f.range g.range
      (s ⊗ₜ[R] (f.range ⊔ g.range).mkQ m)) = _
  rw [ScalarExtensionQuotient318.twoImageEquivalence_tmul]
  rfl
end TwoChartCokernelBaseChange318
