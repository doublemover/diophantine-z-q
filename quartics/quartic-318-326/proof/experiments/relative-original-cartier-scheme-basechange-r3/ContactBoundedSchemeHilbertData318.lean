module
public import ContactBoundedUniversalFamily318
public section
noncomputable section
namespace ContactBoundedSchemeHilbertData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- Standard bounded-degree whole closed quotients. Rank is allowed to
vary over disconnected coefficient schemes; no decomposition is input. -/
structure Data where
  ideal : (pullback p b).IdealSheafData
  finite : IsFinite (ideal.subschemeι ≫ pullback.snd p b)
  flat : Flat (ideal.subschemeι ≫ pullback.snd p b)
  presentation : LocallyOfFinitePresentation (ideal.subschemeι ≫ pullback.snd p b)
  bound : ∀ x : B, (ideal.subschemeι ≫ pullback.snd p b).finrank x≤N
attribute [instance] Data.finite Data.flat Data.presentation
@[ext] lemma Data.ext {D E : Data c N b} (h : D.ideal=E.ideal) : D=E := by
  cases D
  cases E
  cases h
  rfl
abbrev projection (D : Data c N b) := D.ideal.subschemeι ≫ pullback.snd p b
end ContactBoundedSchemeHilbertData318
