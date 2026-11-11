module
public import OriginalKernelScalarExtension318
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public section
noncomputable section
namespace OriginalFreePresentationBaseChange318
open TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (N : Type w) (M : Type z) [AddCommGroup N] [AddCommGroup M] [Module A N] [Module B M]
  (e : B ⊗[A] N ≃ₗ[B] M) (ρ : N → M)
  (hρ : ∀ x : N, e ((1 : B) ⊗ₜ[A] x) = ρ x)
  {ι : Type t} (g : ι → N)

/-- Canonical extension of the ORIGINAL free presentation basis. -/
@[expose] def freeEquivalence : B ⊗[A] (ι →₀ A) ≃ₗ[B] (ι →₀ B) :=
  ((Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).baseChange B).repr

lemma freeEquivalence_basis (i : ι) :
    freeEquivalence A B ((1 : B) ⊗ₜ[A] (Finsupp.single i 1 : ι →₀ A)) =
      Finsupp.single i 1 := by
  change ((Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).baseChange B).repr
    ((Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).baseChange B i) = _
  exact Module.Basis.repr_self _ i

@[expose] def original := Finsupp.linearCombination A g
@[expose] def localized := Finsupp.linearCombination B (fun i => ρ (g i))

include hρ in
/-- The actual original section-unit formula pins the entire free
presentation square; checking only dimensions is unnecessary. -/
lemma square : (localized B N M ρ g).comp (freeEquivalence A B).toLinearMap =
    e.toLinearMap.comp ((original A N g).baseChange B) := by
  apply ((Finsupp.basisSingleOne : Module.Basis ι A (ι →₀ A)).baseChange B).ext
  intro i
  change localized B N M ρ g
    (freeEquivalence A B ((1 : B) ⊗ₜ[A] Finsupp.single i 1)) =
      e ((1 : B) ⊗ₜ[A] original A N g (Finsupp.single i 1))
  rw [freeEquivalence_basis]
  simpa only [original,localized,Finsupp.linearCombination_single,one_smul] using (hρ (g i)).symm

/-- Actual chart relations map to the single original localized kernel. -/
@[expose] def kernelUnit : LinearMap.ker (original A N g) →
    LinearMap.ker (localized B N M ρ g) :=
  OriginalKernelScalarExtension318.unit A B (ι →₀ A) N (ι →₀ B) M
    (original A N g) (localized B N M ρ g) (freeEquivalence A B) e
    (square A B N M e ρ hρ g)

include hρ in
lemma kernel_span (hg : Function.Surjective (original A N g)) :
    Submodule.span B (Set.range (kernelUnit A B N M e ρ hρ g)) = ⊤ :=
  OriginalKernelScalarExtension318.span A B (ι →₀ A) N (ι →₀ B) M
    (original A N g) (localized B N M ρ g) (freeEquivalence A B) e
    (square A B N M e ρ hρ g) hg
end OriginalFreePresentationBaseChange318
