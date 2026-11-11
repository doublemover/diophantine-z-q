module
public import UniversallyInjectiveCokernelFlat318
public import Mathlib.Data.Finset.Union
public section
noncomputable section
namespace FiniteRetractionTensor318
universe u
open TensorProduct
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- Only finitely many right factors need be fixed to fix a particular
tensor. This uses actual tensors, not a freeness assumption on N. -/
lemma finite_support (N : Type u) [AddCommGroup N] [Module R N]
    (x : N ⊗[R] A) :
    ∃ s : Finset A, ∀ h : A →ₗ[R] A,
      (∀ a ∈ s, h a = a) → h.lTensor N x = x := by
  classical
  induction x with
  | tmul n a =>
    refine ⟨{a}, ?_⟩
    intro h hh
    simp [hh a (Finset.mem_singleton_self a)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, ?_⟩
    intro h hh
    rw [map_add, hs h (fun a ha => hh a (Finset.mem_union_left t ha)),
      ht h (fun a ha => hh a (Finset.mem_union_right s ha))]

/-- Finite local retractions produce universal tensor injectivity.
There is no finiteness or Noetherian assumption on the base or N. -/
lemma tensor_injective (f : A →ₗ[R] B)
    (hlocal : ∀ s : Finset A, ∃ g : B →ₗ[R] A, ∀ a ∈ s, g (f a) = a)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  obtain ⟨s, hs⟩ := finite_support N x
  obtain ⟨g, hg⟩ := hlocal s
  have hfix : (g.comp f).lTensor N x = x := hs (g.comp f) hg
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, show f.lTensor N x = 0 from hx,
    map_zero] at hfix
  exact hfix.symm

/-- This sufficient splitting condition feeds the genuine flat-cokernel
criterion. Its finite retractions must still be constructed, rather
than replaced by pointwise field injectivity. -/
lemma cokernel_flat {Q : Type u} [AddCommGroup Q] [Module R Q]
    (f : A →ₗ[R] B) (q : B →ₗ[R] Q)
    (he : Function.Exact f q) (hq : Function.Surjective q) [Module.Flat R B]
    (hlocal : ∀ s : Finset A, ∃ g : B →ₗ[R] A, ∀ a ∈ s, g (f a) = a) :
    Module.Flat R Q :=
  UniversallyInjectiveCokernelFlat318.flat f q he hq (tensor_injective f hlocal)
end FiniteRetractionTensor318
