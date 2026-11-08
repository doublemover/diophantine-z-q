module
public import NormalAffineBasis318
public import FifthChartNorm318
public section
noncomputable section
namespace FifthTargetNormalBasis318
open AlgebraicGeometry CategoryTheory
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance targetIntegral : IsIntegral Target :=
  FifthCompletedProper318.target_proper_integral.2
/-- The two whole normal affine charts cover the actual fifth completed target. -/
theorem chart_cover (x : Target) : ∃ b : Bool, x ∈ FifthChartNorm318.chartOpen b := by
  rcases WeierstrassGluing318.charts_cover A B x with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩
/-- Every target point in every open has a smaller normal affine neighborhood,
using the actual finite and infinity chart section rings. -/
theorem hasBasis : NormalAffineBasis318.HasBasis Target :=
  NormalAffineBasis318.of_cover Target FifthChartNorm318.chartOpen chart_cover
    FifthChartNorm318.chart_affine FifthChartNorm318.chart_normal
end FifthTargetNormalBasis318
