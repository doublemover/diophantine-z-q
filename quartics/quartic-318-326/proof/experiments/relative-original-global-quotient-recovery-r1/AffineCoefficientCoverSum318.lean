module
public import AffineCoefficientCover318
public section
noncomputable section
namespace AffineCoefficientCoverSum318
open AlgebraicGeometry CategoryTheory
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (C D : AffineCoefficientCover318.Data R S)
/-- The combined WHOLE coefficient cover retains both original systems
literally; it does not require a distinguished common localization. -/
@[expose] def sum : AffineCoefficientCover318.Data R S where
  Index := C.Index ⊕ D.Index
  ring := Sum.elim C.ring D.ring
  algebra i := by cases i with | inl i => exact C.algebra i | inr j => exact D.algebra j
  coefficient i := by cases i with | inl i => exact C.coefficient i | inr j => exact D.coefficient j
  open_map i := by cases i with | inl i => exact C.open_map i | inr j => exact D.open_map j
  covers x := by
    obtain ⟨i,hi⟩ := C.covers x
    exact ⟨Sum.inl i,hi⟩
end AffineCoefficientCoverSum318
