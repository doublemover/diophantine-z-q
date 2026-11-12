module
public import OriginalUniversalPrincipalRegular318
public import ContactGeneratedLocalUniversalRegular318
public import ContactUniversalZeroChartRelabel318
public section
noncomputable section
namespace ContactUniversalPrincipalEquations318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318
open ContactGeneratedLocalUniversalRegular318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "M" => generatedLine R c L
local notation "P" => ContactGeneratedLocalUniversalRegular318.P R c L
local instance : Module R P := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) M ⊤
local instance : Module.Finite R P :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c M (properties R c L).1).1
local instance : Module.Projective R P :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c M (properties R c L).1).2
local notation "S" => CommRingCat.of (ProjectiveSectionParameter318.algebra R P)

/-- Actual regular principal equations on the produced full finite-chart
parameter cover. Generation, positive twist, H1 vanishing, finite projectivity,
and each line frame have all been constructed, not passed as hypotheses. -/
theorem finite_covering_equations :
    OriginalUniversalPrincipalRegular318.HasCoveringEquations R
      (CommRingCat.of (R ⊗[ℚ] finiteRing c)) (finiteLine R c M) P
      (ContactPositiveChartEvaluation318.finiteRestriction R c M) :=
  OriginalUniversalPrincipalRegular318.covering_equations R
    (CommRingCat.of (R ⊗[ℚ] finiteRing c)) (finiteLine R c M) P
    (ContactPositiveChartEvaluation318.finiteRestriction R c M) (properties R c L).2.1

/-- Independent reciprocal-chart counterpart on the actual infinity
line. The finite-chart frame is never substituted for the infinity line. -/
theorem infinity_covering_equations :
    OriginalUniversalPrincipalRegular318.HasCoveringEquations R
      (CommRingCat.of (R ⊗[ℚ] infinityRing c)) (infinityLine R c M) P
      (ContactPositiveChartEvaluation318.infinityRestriction R c M) :=
  OriginalUniversalPrincipalRegular318.covering_equations R
    (CommRingCat.of (R ⊗[ℚ] infinityRing c)) (infinityLine R c M) P
    (ContactPositiveChartEvaluation318.infinityRestriction R c M) (properties R c L).2.2
end ContactUniversalPrincipalEquations318
