module
public import ContactFixedDegreeUniversalRecovery318
public section
noncomputable section
namespace ContactHilbertData318
open AlgebraicGeometry CategoryTheory
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ)
/-- Standard full original quotient data: finite, flat and locally of
finite presentation for the WHOLE closed-family projection. No Cartier,
chart support, chosen local presentation or classifying point is assumed. -/
structure Datum where
  ideal : (ContactRelativeLinearOpenChart318.curve S c).IdealSheafData
  finite : IsFinite (ideal.subschemeι ≫ ContactRelativeLinearOpenChart318.projection S c)
  flat : Flat (ideal.subschemeι ≫ ContactRelativeLinearOpenChart318.projection S c)
  presentation : LocallyOfFinitePresentation (ideal.subschemeι ≫ ContactRelativeLinearOpenChart318.projection S c)
attribute [instance] Datum.finite Datum.flat Datum.presentation
variable (D : Datum S c)
abbrev projection := D.ideal.subschemeι ≫ ContactRelativeLinearOpenChart318.projection S c
@[expose] def degree : PrimeSpectrum S → ℕ := (projection S c D).finrank
@[expose] def FixedRank (n : ℕ) := {D : Datum S c // ∀ x,degree S c D x=n}
@[expose] def BoundedRank (N : ℕ) := {D : Datum S c // ∀ x,degree S c D x≤N}
@[ext] lemma Datum.ext {D E : Datum S c} (h : D.ideal=E.ideal) : D=E := by
  cases D
  cases E
  cases h
  rfl
end ContactHilbertData318
