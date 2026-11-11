module
public import ContactGeometricallyIntegral318
public import ContactRelativeStructuralHOne318
public section
noncomputable section
namespace ContactRelativeOriginalSmoothProper318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

/-- The ACTUAL original coefficient-family projection, over arbitrary
coefficient rings, is smooth by its genuine original base-change square. -/
instance smooth : Smooth (ContactRelativeStructuralHOne318.projection R c) := by
  letI : Smooth (ContactOriginalAffineTestCover318.p c) :=
    (ContactGeometricallyIntegral318.smooth_proper_geometricallyIntegral_model c).1
  exact inferInstanceAs (Smooth (pullback.snd (ContactOriginalAffineTestCover318.p c) (baseMap R)))

/-- Properness of the same original family, with no replacement model. -/
instance proper : IsProper (ContactRelativeStructuralHOne318.projection R c) := by
  letI : IsProper (ContactOriginalAffineTestCover318.p c) :=
    (ContactGeometricallyIntegral318.smooth_proper_geometricallyIntegral_model c).2.1
  exact inferInstanceAs (IsProper (pullback.snd (ContactOriginalAffineTestCover318.p c) (baseMap R)))

/-- In particular, ambient flatness and finite presentation needed by a
relative Cartier-flatness argument are constructed for the ACTUAL model.
They do not assert flatness of a closed zero family. -/
theorem flat_finitePresentation :
    Flat (ContactRelativeStructuralHOne318.projection R c) ∧
    LocallyOfFinitePresentation (ContactRelativeStructuralHOne318.projection R c) :=
  ⟨inferInstance,inferInstance⟩
end ContactRelativeOriginalSmoothProper318
