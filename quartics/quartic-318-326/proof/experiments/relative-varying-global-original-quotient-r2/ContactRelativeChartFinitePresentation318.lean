module
public import RelativePolynomialFinitePresentation318
public import OriginalFinitePresentationRestriction318
public import ContactOriginalRelativePolynomialCharts318
public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ContactRelativeChartFinitePresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (Polynomial ℚ) (finiteRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : Module.Finite (Polynomial ℚ) (finiteRing c) :=
  (ContactKummerOrder318.source_finite_free c).1

/-- Noetherianity is used only on the fixed rational model before
coefficient extension, never asserted of the arbitrary coefficient ring R. -/
local instance finite_old : Module.FinitePresentation (Polynomial ℚ) (finiteRing c) :=
  Module.finitePresentation_of_finite (Polynomial ℚ) (finiteRing c)
local instance infinity_old : Module.FinitePresentation (Polynomial ℚ) (infinityRing c) :=
  Module.finitePresentation_of_finite (Polynomial ℚ) (infinityRing c)

/-- Both ACTUAL whole polynomial chart modules of every line over every
R-test are finitely presented, even when R is nonreduced/non-Noetherian. -/
theorem finite_chart : Module.FinitePresentation (Polynomial R) (finiteSections R c L) :=
  OriginalFinitePresentationRestriction318.sections (CommRingCat.of (Polynomial R))
    (CommRingCat.of (RelativeOriginalPolynomialAlgebra318.original ℚ R (finiteRing c)))
    (LineSheafPullback318.line (finiteInto R c) L)

theorem infinity_chart : Module.FinitePresentation (Polynomial R) (infinitySections R c L) :=
  OriginalFinitePresentationRestriction318.sections (CommRingCat.of (Polynomial R))
    (CommRingCat.of (RelativeOriginalPolynomialAlgebra318.original ℚ R (infinityRing c)))
    (LineSheafPullback318.line (infinityInto R c) L)
end ContactRelativeChartFinitePresentation318
