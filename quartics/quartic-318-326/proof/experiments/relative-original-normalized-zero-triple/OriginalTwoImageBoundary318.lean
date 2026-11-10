module
public import Mathlib.LinearAlgebra.Quotient.Defs
public section
namespace OriginalTwoImageBoundary318
universe u v w z
variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {A : Type w} [AddCommGroup A] [Module R A]
  {B : Type z} [AddCommGroup B] [Module R B]
  (f : A →ₗ[R] M) (g : B →ₗ[R] M)

/-- The sum of the two ORIGINAL image submodules is the image of their
literal restriction difference, with its sign retained. -/
lemma mem_iff (x : M) : x ∈ f.range ⊔ g.range ↔ ∃ a b, f a - g b = x := by
  constructor
  · intro hx
    obtain ⟨y,⟨a,rfl⟩,z,⟨b,rfl⟩,h⟩ := Submodule.mem_sup.mp hx
    refine ⟨a,-b,?_⟩
    simpa only [map_neg,sub_neg_eq_add] using h
  · rintro ⟨a,b,rfl⟩
    exact Submodule.mem_sup.mpr ⟨f a,⟨a,rfl⟩,-g b,g.range.neg_mem ⟨b,rfl⟩,by rw [sub_eq_add_neg]⟩
end OriginalTwoImageBoundary318
