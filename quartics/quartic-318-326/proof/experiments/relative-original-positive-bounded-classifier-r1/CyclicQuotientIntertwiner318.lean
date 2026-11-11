module
public import OriginalFreeQuotientAction318
public section
noncomputable section
namespace CyclicQuotientIntertwiner318
open CyclicQuotientEvaluation318
universe u
variable {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (ρ : A →ₐ[R] Module.End R M) (σ : A →ₐ[R] Module.End R N)
  (v : M) (w : N) (e : M ≃ₗ[R] N)

/-- A genuine basis-change intertwiner preserving the cyclic vector
preserves the entire evaluation map. This is the overlap direction used
by varying quotient charts, over all coefficient rings. -/
lemma evaluation_intertwines
    (he : ∀ a x, e (ρ a x) = σ a (e x)) (hv : e v = w) (a : A) :
    e (evaluation ρ v a) = evaluation σ w a := by
  change e (ρ a v) = σ a w
  rw [he,hv]

lemma ideal_eq
    (he : ∀ a x, e (ρ a x) = σ a (e x)) (hv : e v = w) :
    ideal ρ v = ideal σ w := by
  ext a
  change evaluation ρ v a = 0 ↔ evaluation σ w a = 0
  constructor
  · intro h
    rw [← evaluation_intertwines ρ σ v w e he hv a,h,map_zero]
  · intro h
    apply e.injective
    rw [evaluation_intertwines ρ σ v w e he hv a,h,map_zero]

/-- Surjectivity survives the SAME invertible change of frame. -/
lemma cyclic_transport
    (he : ∀ a x, e (ρ a x) = σ a (e x)) (hv : e v = w)
    (h : Function.Surjective (evaluation ρ v)) :
    Function.Surjective (evaluation σ w) := by
  intro y
  obtain ⟨a,ha⟩ := h (e.symm y)
  refine ⟨a,?_⟩
  rw [← evaluation_intertwines ρ σ v w e he hv a,ha,e.apply_symm_apply]
end CyclicQuotientIntertwiner318
