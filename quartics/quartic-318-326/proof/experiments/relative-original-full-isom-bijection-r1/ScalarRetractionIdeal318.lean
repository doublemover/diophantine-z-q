module
public import FiniteRetractionTensor318
public import Mathlib.RingTheory.Ideal.Maximal
public section
noncomputable section
namespace ScalarRetractionIdeal318
universe u
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- Actual scalar retractions on the specified finite set form an ideal.
This permits different finite matrices and different retractions over
different maximal ideals; no global choice of one matrix is required. -/
@[expose] def scalars (f : A →ₗ[R] B) (s : Finset A) : Ideal R where
  carrier := {r | ∃ g : B →ₗ[R] A, ∀ a ∈ s, g (f a) = r • a}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro r t ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨g+h, ?_⟩
    intro a ha
    simp only [LinearMap.add_apply, hg a ha, hh a ha, add_smul]
  smul_mem' := by
    rintro r t ⟨g, hg⟩
    refine ⟨r • g, ?_⟩
    intro a ha
    simp only [LinearMap.smul_apply, hg a ha, smul_eq_mul, mul_smul]

lemma retraction_of_not_contained (f : A →ₗ[R] B) (s : Finset A)
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ r ∈ scalars f s, r ∉ m) :
    ∃ g : B →ₗ[R] A, ∀ a ∈ s, g (f a) = a := by
  have htop : scalars f s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (scalars f s) hne
    obtain ⟨r, hr, hrm⟩ := h m hm
    exact hrm (hle hr)
  have hone : (1 : R) ∈ scalars f s := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := hone
  exact ⟨g, fun a ha => by simpa only [one_smul] using hg a ha⟩

/-- A scalar retraction nonvanishing at EACH maximal ideal is enough
for tensor injectivity over arbitrary modules. All ring nilpotents are
retained; the conclusion does not assume the base is reduced. -/
lemma tensor_injective (f : A →ₗ[R] B)
    (h : ∀ s : Finset A, ∀ m : Ideal R, m.IsMaximal →
      ∃ r ∈ scalars f s, r ∉ m)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) :=
  FiniteRetractionTensor318.tensor_injective f
    (fun s => retraction_of_not_contained f s (h s)) N

lemma cokernel_flat {Q : Type u} [AddCommGroup Q] [Module R Q]
    (f : A →ₗ[R] B) (q : B →ₗ[R] Q)
    (he : Function.Exact f q) (hq : Function.Surjective q) [Module.Flat R B]
    (h : ∀ s : Finset A, ∀ m : Ideal R, m.IsMaximal →
      ∃ r ∈ scalars f s, r ∉ m) : Module.Flat R Q :=
  UniversallyInjectiveCokernelFlat318.flat f q he hq (tensor_injective f h)
end ScalarRetractionIdeal318
