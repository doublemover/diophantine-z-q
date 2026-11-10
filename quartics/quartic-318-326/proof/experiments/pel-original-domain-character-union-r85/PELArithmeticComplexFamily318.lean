module
public import PELPrincipalBaseHolomorphy318
public section
noncomputable section
namespace PELArithmeticComplexFamily318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open PELJointComplexAtlas318 PELPrincipalThreeFreeAction318 PELPrincipalThreeCovering318
open PELPrincipalBaseHolomorphy318 HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

theorem principal_total_holomorphic (u : principalThree) :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (fun p : Total => u • p) :=
  PELJointArithmeticHolomorphy318.totalAction_holomorphic u.val (determinant u)

/-- The base atlas is built on the LITERAL principal-three orbit quotient,
from actual inverse covering branches and the original complex parameter. -/
@[expose,instance_reducible] def arithmeticBaseCharts : ChartedSpace ℂ ArithmeticBase :=
  quotientCharts baseQuotient base_covering

/-- The total atlas uses the original joint complex threefold and its
actual arithmetic action, not a product complex structure on its real trivialization. -/
@[expose,instance_reducible] def arithmeticTotalCharts : ChartedSpace Ambient ArithmeticTotal :=
  quotientCharts totalQuotient total_covering

theorem arithmeticBase_manifold :
    letI := arithmeticBaseCharts
    IsManifold 𝓘(ℂ,ℂ) ω ArithmeticBase :=
  quotient_manifold baseQuotient base_covering principal_base_holomorphic

theorem arithmeticTotal_manifold :
    letI := arithmeticTotalCharts
    IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal :=
  quotient_manifold totalQuotient total_covering principal_total_holomorphic

local instance : ChartedSpace ℂ ArithmeticBase := arithmeticBaseCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω ArithmeticBase := arithmeticBase_manifold
local instance : ChartedSpace Ambient ArithmeticTotal := arithmeticTotalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal := arithmeticTotal_manifold

theorem baseQuotient_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω baseQuotient :=
  projection_holomorphic baseQuotient base_covering principal_base_holomorphic

theorem totalQuotient_holomorphic :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω totalQuotient :=
  projection_holomorphic totalQuotient total_covering principal_total_holomorphic

/-- A genuine holomorphic family on the actual arithmetic quotient. The
entire commuting square is used, not a pointwise or fiberwise holomorphy inference. -/
theorem arithmeticProjection_holomorphic :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,ℂ) ω arithmeticProjection := by
  apply descended_holomorphic totalQuotient total_covering principal_total_holomorphic
    arithmeticProjection (fun p : Total => baseQuotient p.1)
  · exact baseQuotient_holomorphic.comp original_projection_holomorphic
  · exact arithmetic_projection_square
end PELArithmeticComplexFamily318
