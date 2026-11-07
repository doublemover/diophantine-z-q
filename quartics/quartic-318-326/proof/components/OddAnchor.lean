module
public import QuarticOptimization
public section
namespace OddAnchor

/-- The local-to-global logical step behind the affine parity anchor.
The elliptic-curve valuation statements supplying hA, hT2 and hT3 are
explicit hypotheses; this theorem does not assert them. -/
theorem affine_anchor_iff {K : Type*} [Ring K] (R2 R3 : Subring K)
    (a t : K) (OddLabels : Prop) (hA : a ∈ R2)
    (hT2 : t ∈ R2 ↔ OddLabels) (hT3 : OddLabels → t ∈ R3) :
    (a+t ∈ R2 ∧ a+t ∈ R3) ↔ (OddLabels ∧ a ∈ R3) := by
  constructor
  · rintro ⟨h2,h3⟩
    have ht : t ∈ R2 := by simpa using R2.sub_mem h2 hA
    have ho := hT2.mp ht
    exact ⟨ho, by simpa using R3.sub_mem h3 (hT3 ho)⟩
  · rintro ⟨ho,ha⟩
    exact ⟨R2.add_mem hA (hT2.mpr ho), R3.add_mem ha (hT3 ho)⟩

theorem norm_square_identity (a b : ℚ) :
    (a^2+2*b^2)^2-2*(2*a*b)^2=(a^2-2*b^2)^2 := by ring

theorem norm_square_positive (a b : ℚ) (h : a^2-2*b^2 ≠ 0) :
    0 < (a^2+2*b^2)^2-2*(2*a*b)^2 := by
  rw [norm_square_identity]
  exact sq_pos_of_ne_zero h

end OddAnchor
