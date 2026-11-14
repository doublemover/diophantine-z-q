module
public import ContactNormalizedOriginalClass318
public import RelativeClassSheafPoint318
public section
noncomputable section
namespace ContactNormalizedAbelFiber318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "p" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c L hz

/-- The global normalized divisor family lies in the ORIGINAL line's
Abel fiber in the existing associated fppf sheaf. This is equality of
actual sheaf sections over the whole parameter scheme, including all
nonreduced tests; the absolute tautological twist is not discarded by
an unjustified global line isomorphism. -/
theorem original_sheaf_class : RelativeClassSheafPoint318.value p b
    (OriginalLineAbelTransformation318.point p b D)=
    RelativeClassSheafPoint318.value p b
      (RelativeClassSheafPoint318.original p b (classOf L)) := by
  apply RelativeClassSheafPoint318.original_of_cover p b
    (ContactNormalizedSectionParameter318.cover R c L hz)
  intro i
  exact ContactNormalizedOriginalClass318.relative_chart R c L hz i
end ContactNormalizedAbelFiber318
