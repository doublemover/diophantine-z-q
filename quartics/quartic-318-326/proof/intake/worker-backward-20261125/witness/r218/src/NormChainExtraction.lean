module
public import NormChainValuation
public section
namespace NormChainExtraction

/-- The exact integer valuation recursion after odd-parity exclusion of
cancellation. Each pair is (required order, valuation of the tested leaf). -/
@[expose] def chain (R initial : ℤ) : List (ℤ × ℤ) → ℤ
  | [] => initial
  | (m,leaf)::rest => chain R (min (2*initial) (2*leaf-(2*m-1)*R)) rest

theorem unequal_summands (R previous m leaf : ℤ) (hR : Odd R) :
    2*previous ≠ 2*leaf-(2*m-1)*R := by
  intro h
  obtain ⟨k,hk⟩ := hR
  have he : 2*(previous-leaf+m*R)=R := by nlinarith
  omega

theorem extract (R initial : ℤ) (leaves : List (ℤ × ℤ))
    (hR : 1 ≤ R) (hm : ∀ p ∈ leaves, 1 ≤ p.1)
    (hfinal : 0 < 2*chain R initial leaves+R) :
    0 < 2*initial+R ∧ ∀ p ∈ leaves, p.1 ≤ p.2 := by
  induction leaves generalizing initial with
  | nil => simpa [chain] using hfinal
  | cons p rest ih =>
    obtain ⟨m,leaf⟩ := p
    have htail : ∀ p ∈ rest, 1 ≤ p.1 := by
      intro p hp
      exact hm p (List.mem_cons_of_mem _ hp)
    have hfirst : 1 ≤ m := hm (m,leaf) (by simp)
    obtain ⟨hstep,hrest⟩ := ih _ htail (by simpa [chain] using hfinal)
    obtain ⟨hinit,hleaf⟩ := NormChainValuation.backward_step R m
      (min (2*initial) (2*leaf-(2*m-1)*R)) initial leaf
      hR hfirst hstep (min_le_left _ _) (min_le_right _ _)
    refine ⟨hinit,?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · simpa [hp] using hleaf
    · exact hrest p hp

theorem nonpositive (R initial : ℤ) (leaves : List (ℤ × ℤ))
    (hinitial : initial ≤ 0) : chain R initial leaves ≤ 0 := by
  induction leaves generalizing initial with
  | nil => exact hinitial
  | cons p rest ih =>
    apply ih
    exact le_trans (min_le_left _ _) (by omega)

theorem contact_positive (R : ℤ) (leaves : List (ℤ × ℤ))
    (hfinal : 0 < 2*chain R 0 leaves+R) : 0 < R := by
  have hw := nonpositive R 0 leaves (by omega)
  omega

/-- A reciprocal-trace pole gives the required order for every leaf at one
common split place. The exact trace inequality and exact chain recursions
are hypotheses, rather than hidden appeals to a valuation library. -/
theorem split_place_extract (R trace : ℤ) (left right : List (ℤ × ℤ))
    (hleft : ∀ p ∈ left, 1 ≤ p.1) (hright : ∀ p ∈ right, 1 ≤ p.1)
    (htrace : min (chain R 0 left) (chain R 0 right) ≤ trace)
    (hpole : 0 < 2*(chain R 0 left+chain R 0 right-trace)+R) :
    (∀ p ∈ left, p.1 ≤ p.2) ∨ (∀ p ∈ right, p.1 ≤ p.2) := by
  rcases NormChainValuation.reciprocal_trace_one_place R
    (chain R 0 left) (chain R 0 right) trace htrace hpole with hl | hr
  · exact Or.inl ((extract R 0 left (by have := contact_positive R left hl; omega)
      hleft hl).2)
  · exact Or.inr ((extract R 0 right (by have := contact_positive R right hr; omega)
      hright hr).2)

end NormChainExtraction
