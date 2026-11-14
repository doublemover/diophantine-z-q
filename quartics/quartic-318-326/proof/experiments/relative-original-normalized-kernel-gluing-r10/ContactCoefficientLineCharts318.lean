module
public import ContactRelativeCoefficientChange318
public import OriginalCoefficientChartLine318
public section
noncomputable section
namespace ContactCoefficientLineCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactRelativeCoefficientChange318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- The global line that H1 base change must use. -/
abbrev pulledLine := LineSheafPullback318.line (curveMap R S f c) L

/-- All three section comparisons retain the same original global L
and its literal pullback, with no trivialization or basis assumption. -/
abbrev finiteComparison := OriginalCoefficientChartLine318.sectionsComparison
  (curveMap R S f c) (finiteRingMap R S f c) (finiteInto R c) (finiteInto S c)
  (finite_square R S f c) L
abbrev infinityComparison := OriginalCoefficientChartLine318.sectionsComparison
  (curveMap R S f c) (infinityRingMap R S f c) (infinityInto R c) (infinityInto S c)
  (infinity_square R S f c) L
abbrev overlapComparison := OriginalCoefficientChartLine318.sectionsComparison
  (curveMap R S f c) (overlapRingMap R S f c) (into R c) (into S c)
  (overlap_square R S f c) L

abbrev finiteRestriction := OriginalCoefficientChartLine318.originalRestriction
  (curveMap R S f c) (finiteRingMap R S f c) (finiteInto R c) (finiteInto S c)
  (finite_square R S f c) L
abbrev infinityRestriction := OriginalCoefficientChartLine318.originalRestriction
  (curveMap R S f c) (infinityRingMap R S f c) (infinityInto R c) (infinityInto S c)
  (infinity_square R S f c) L
abbrev overlapRestriction := OriginalCoefficientChartLine318.originalRestriction
  (curveMap R S f c) (overlapRingMap R S f c) (into R c) (into S c)
  (overlap_square R S f c) L

lemma overlap_unit (m : ContactOriginalRelativeLineOverlap318.originalSections R c L) :
    (overlapComparison R S f c L).hom
      ((ModuleCat.extendRestrictScalarsAdj (overlapRingMap R S f c).hom).unit.app _ m) =
        overlapRestriction R S f c L m :=
  OriginalCoefficientChartLine318.unit _ _ _ _ _ _ m
end ContactCoefficientLineCharts318
