module
public import ContactHilbertBaseChange318
public section
noncomputable section
namespace ContactSchemeHilbertData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- STANDARD original fixed-rank quotients over an arbitrary coefficient
SCHEME, with all conditions on the whole closed-family projection. -/
structure Data where
  ideal : (pullback p b).IdealSheafData
  finite : IsFinite (ideal.subschemeι ≫ pullback.snd p b)
  flat : Flat (ideal.subschemeι ≫ pullback.snd p b)
  presentation : LocallyOfFinitePresentation (ideal.subschemeι ≫ pullback.snd p b)
  rank : ∀ x : B, (ideal.subschemeι ≫ pullback.snd p b).finrank x=n
attribute [instance] Data.finite Data.flat Data.presentation
@[ext] lemma Data.ext {D E : Data c n b} (h : D.ideal=E.ideal) : D=E := by
  cases D
  cases E
  cases h
  rfl
variable (D : Data c n b)
abbrev projection := D.ideal.subschemeι ≫ pullback.snd p b
end ContactSchemeHilbertData318
