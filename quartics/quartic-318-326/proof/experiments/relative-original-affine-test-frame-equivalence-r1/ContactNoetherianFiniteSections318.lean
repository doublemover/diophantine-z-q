module
public import ContactOriginalSectionKernel318
public import Mathlib.RingTheory.Noetherian.Basic
public section
noncomputable section
namespace ContactNoetherianFiniteSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactOriginalSectionKernel318
variable (R : CommRingCat.{0}) [Algebra ℚ R] [hnoeth : IsNoetherianRing R]
  (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
include hnoeth in
/-- Actual H0 of EVERY original line is finite over a Noetherian
coefficient ring: it is the genuine kernel inside the produced finite
projective complex. No H1 vanishing or H0 projectivity is asserted. -/
lemma finite : Module.Finite R Γ(L.object,⊤) := by
  letI : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
  letI : IsNoetherian R (zeroTerm R c L) := inferInstance
  letI : Module.Finite R (LinearMap.ker (boundary R c L)) := inferInstance
  exact Module.Finite.equiv (ContactRelativeFiniteCohomologyModel318.hzero R c L (bound R c L)).symm
end ContactNoetherianFiniteSections318
