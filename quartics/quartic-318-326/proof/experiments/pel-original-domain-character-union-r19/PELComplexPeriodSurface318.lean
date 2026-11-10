module
public import PELPeriodRiemannForm318
public import DiscreteComplexPeriodMaps318
public section
noncomputable section
namespace PELComplexPeriodSurface318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open DiscreteComplexPeriodAtlas318 DiscreteComplexPeriodMaps318
open scoped Manifold ContDiff
set_option maxHeartbeats 1000000
variable (τ : ℂ) (hτ : 0<τ.im)
abbrev Periods := periodSubgroup representation order τ
abbrev Surface := PeriodQuotient representation order τ
local instance : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ

/-- The original quaternion order quotient is now a genuine complex
surface. It is not an algebraic abelian surface or PEL moduli scheme yet. -/
@[expose, instance_reducible] def surfaceCharts : ChartedSpace ComplexVectors (Surface τ) :=
  chartedSpace (Periods τ)

theorem surface_manifold :
    letI := surfaceCharts τ hτ
    IsManifold 𝓘(ℂ,ComplexVectors) ω (Surface τ) :=
  complex_manifold (Periods τ)

include hτ in
theorem surface_compact : CompactSpace (Surface τ) :=
  PELOriginalPeriodLattice318.original_compact τ hτ

include hτ in
theorem surface_hausdorff : T2Space (Surface τ) :=
  quotient_hausdorff (Periods τ)

theorem original_projection_holomorphic :
    letI := surfaceCharts τ hτ
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (projection (Periods τ)) :=
  projection_contMDiff (Periods τ)

/-- Every element of the exact original integral quaternion order acts by a
holomorphic endomorphism of this same compact complex period surface. -/
theorem original_action_holomorphic (a : order) :
    letI := surfaceCharts τ hτ
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (orderEnd representation order τ a) :=
  descended_linear_contMDiff (Periods τ) (leftLinear (representation a))
    (orderEnd representation order τ a) (fun _ => rfl)
end PELComplexPeriodSurface318
