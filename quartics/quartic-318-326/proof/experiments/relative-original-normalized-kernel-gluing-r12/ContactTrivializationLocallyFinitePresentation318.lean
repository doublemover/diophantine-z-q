module
public import ContactArbitrarySectionFinitePresentation318
public import ContactTrivializationFullNaturality318
public section
noncomputable section
namespace ContactTrivializationLocallyFinitePresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
open ContactArbitraryNowhereZeroOpen318 ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- The unchanged represented original trivialization open, with its
actual structural map, rather than a new parameter assigned the same points. -/
abbrev projection : scheme R c L ⟶ Spec R := into R c L ≫ parameterProjection R c L

instance locallyFinitePresentation : LocallyOfFinitePresentation (projection R c L) := by
  unfold projection
  infer_instance

/-- The property survives EVERY scheme base change. This is geometric
local finite presentation, not an assertion that H0 is locally free. -/
instance baseChange {T : Scheme.{0}} (f : T ⟶ Spec R) :
    LocallyOfFinitePresentation (pullback.snd (projection R c L) f) := inferInstance
end ContactTrivializationLocallyFinitePresentation318
