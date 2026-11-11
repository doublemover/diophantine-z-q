module
public import OriginalLineFiniteFlatPID318
public import ContactBicanonicalDegree318
public import Mathlib.Algebra.Polynomial.FieldDivision

public section
noncomputable section
namespace ContactOriginalLineFiniteChart318
open AlgebraicGeometry CategoryTheory LineSheafClass318 Polynomial
variable (c : Fin 4 → ℚˣ)

local instance : Module.Finite ℚ[X] (ContactKummerOrder318.SourceOrder c) :=
  (ContactKummerOrder318.source_finite_free c).1
local instance : Module.Free ℚ[X] (ContactKummerOrder318.SourceOrder c) :=
  (ContactKummerOrder318.source_finite_free c).2

variable (L : Line (Spec (CommRingCat.of (ContactKummerOrder318.SourceOrder c))))

/-- The source is the whole original finite chart, including every finite
contact, and the base action is the original t-chart polynomial action. -/
abbrev sections := OriginalLineFiniteFlatPID318.pushed (CommRingCat.of ℚ[X])
  (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) L

instance finite : Module.Finite ℚ[X] (sections c L) :=
  OriginalLineFiniteFlatPID318.finite (CommRingCat.of ℚ[X])
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) L
instance free : Module.Free ℚ[X] (sections c L) :=
  OriginalLineFiniteFlatPID318.free (CommRingCat.of ℚ[X])
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) L

/-- Genuine finite coordinates on every original line over the whole finite
Contact chart; no chosen free-module hypothesis is added. -/
def coordinates : sections c L ≃ₗ[ℚ[X]]
    (Fin (Module.finrank ℚ[X] (sections c L)) → ℚ[X]) :=
  OriginalLineFiniteFlatPID318.coordinates (CommRingCat.of ℚ[X])
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) L

/-- The finite chart is the entire base change of the actual degree-sixteen
Contact map, not a punctured replacement. -/
theorem original_pullback : IsPullback (ContactBicanonicalDegree318.affineMap c)
    (SourceGlobalAffine318.chartEmbedding c) (JLineAtlas318.chart ℚ 1)
    (ContactBicanonicalProjectiveMap318.projectiveMap c) :=
  ContactBicanonicalDegree318.affine_pullback c
end ContactOriginalLineFiniteChart318
