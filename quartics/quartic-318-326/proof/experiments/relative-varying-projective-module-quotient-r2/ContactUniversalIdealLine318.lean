module
public import OriginalUniversalIdealLine318
public import ContactGeneratedLocalUniversalRegular318
public section
noncomputable section
namespace ContactUniversalIdealLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
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

/-- Actual finite-chart zero ideal line on every produced parameter-open
frame, with generation and regularity internally supplied. The map is
literal evaluation of the original line dual, not a rank comparison. -/
@[expose] def finite_dualIdeal
    (r : OriginalPrincipalAffineFrames318.Index (CommRingCat.of (R ⊗[ℚ] finiteRing c))
      (finiteLine R c M)) :=
  OriginalUniversalIdealLine318.dualIdeal R (CommRingCat.of (R ⊗[ℚ] finiteRing c))
    (finiteLine R c M) P (ContactPositiveChartEvaluation318.finiteRestriction R c M)
    (properties R c L).2.1 r

/-- Actual infinity-chart counterpart, retaining its own original
reciprocal line, principal frame map and SAME universal section. -/
@[expose] def infinity_dualIdeal
    (r : OriginalPrincipalAffineFrames318.Index (CommRingCat.of (R ⊗[ℚ] infinityRing c))
      (infinityLine R c M)) :=
  OriginalUniversalIdealLine318.dualIdeal R (CommRingCat.of (R ⊗[ℚ] infinityRing c))
    (infinityLine R c M) P (ContactPositiveChartEvaluation318.infinityRestriction R c M)
    (properties R c L).2.2 r
end ContactUniversalIdealLine318
