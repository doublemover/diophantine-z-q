module
public import TangentMetricContinuity318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 PeterssonQuotient318 DependentFiberBundle318
open HolomorphicCharts318 ActualQuadraticForm318 TangentMetric318 ActualOperatorNorm318
open scoped Manifold ContDiff
namespace MetricOperatorSupremum318
set_option maxHeartbeats 0
variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out

@[expose] def unitBallValues (b:Base (image N)) (q:fibers N b) : Set ℝ :=
  {r|∃u v:TangentSpace 𝓘(ℂ) b,tangentSeminorm N b u≤1 ∧ tangentSeminorm N b v≤1 ∧
    r=‖quadraticEquiv N b q u v‖}

/-- The maximum over the actual metric unit balls is attained and equals
the genuine descended Petersson norm. -/
theorem norm_isGreatest (b:Base (image N)) (q:fibers N b) :
    IsGreatest (unitBallValues N b q) (PeterssonQuotient318.norm (image N) q.val) := by
  constructor
  · exact ⟨unitVector N b,unitVector N b,le_of_eq (unitVector_length N b),
      le_of_eq (unitVector_length N b),(norm_attained N b q).symm⟩
  · rintro r ⟨u,v,hu,hv,rfl⟩
    exact (unit_ball_bound_iff N b q _).mpr le_rfl u v hu hv

/-- Literal supremum/operator-norm equality, with nonemptiness and boundedness
already secured by an actual maximizing pair. -/
theorem operator_norm_eq (b:Base (image N)) (q:fibers N b) :
    sSup (unitBallValues N b q)=PeterssonQuotient318.norm (image N) q.val :=
  (norm_isGreatest N b q).csSup_eq

end MetricOperatorSupremum318
