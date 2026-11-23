module
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Recover the two original integral coefficients on a trivialization of
the actual smooth-locus dualizing square. The half-maps need not descend,
the integral extension need not be unramified, and the base-changed ring
may be disconnected. The only output is membership on this frame, not a
constructor for the fine model, its Néron morphisms or its dualizing line.
-/
public section
namespace OriginalEllipticHalfLatticeDescent318

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Module.FaithfullyFlat A B] [Algebra B C]

private theorem restore {a d : A} (b : B)
    (hh : algebraMap A B a = algebraMap A B d * b) :
    ∃ z : A, a = d * z := by
  let I : Ideal A := Ideal.span ({d} : Set A)
  have hm : a ∈ (I.map (algebraMap A B)).comap (algebraMap A B) := by
    change algebraMap A B a ∈ (Ideal.span ({d} : Set A)).map (algebraMap A B)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨b, hh⟩
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hm
  exact Ideal.mem_span_singleton.mp hm

/-- Over an original affine smooth chart, write each rational coefficient
as aᵢ/dᵢ (in the actual application dᵢ is a power of the residue prime).
The integral half-forms have coefficients u,v only upstairs. Their squares
are compared in the generic ring C *after* pullback in the same frame.
Return the integral coefficients downstairs without averaging or descent
of a choice of half-map. For regular denominators this identifies aᵢ/dᵢ.
-/
theorem restore_original_pair
    (inj : Function.Injective (algebraMap B C))
    (a₀ d₀ a₁ d₁ : A) (u v : B)
    (h₀ : algebraMap B C (algebraMap A B a₀) =
      algebraMap B C (algebraMap A B d₀) * (-(algebraMap B C u ^ 2)))
    (h₁ : algebraMap B C (algebraMap A B a₁) =
      algebraMap B C (algebraMap A B d₁) * (343 * algebraMap B C v ^ 2)) :
    (∃ z₀ : A, a₀ = d₀ * z₀) ∧ (∃ z₁ : A, a₁ = d₁ * z₁) := by
  constructor
  · apply restore (B := B) (-(u ^ 2))
    apply inj
    rw [map_mul, map_neg, map_pow]
    exact h₀
  · apply restore (B := B) (343 * v ^ 2)
    apply inj
    simp only [map_mul, map_pow, map_ofNat]
    exact h₁

end OriginalEllipticHalfLatticeDescent318

#print axioms OriginalEllipticHalfLatticeDescent318.restore_original_pair
