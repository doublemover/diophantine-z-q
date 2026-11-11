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
abbrev Periods (τ : ℂ) := periodSubgroup representation order τ
abbrev Surface (τ : ℂ) := PeriodQuotient representation order τ

/-- The original quaternion order quotient is now a genuine complex
surface. It is not an algebraic abelian surface or PEL moduli scheme yet. -/
@[expose, instance_reducible] def surfaceCharts (τ : ℂ) (hτ : 0<τ.im) :
    ChartedSpace ComplexVectors (Surface τ) := by
  letI : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  exact chartedSpace (Periods τ)

theorem surface_manifold (τ : ℂ) (hτ : 0<τ.im) :
    letI := surfaceCharts τ hτ
    IsManifold 𝓘(ℂ,ComplexVectors) ω (Surface τ) := by
  letI : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  exact complex_manifold (Periods τ)

theorem surface_compact (τ : ℂ) (hτ : 0<τ.im) : CompactSpace (Surface τ) :=
  PELOriginalPeriodLattice318.original_compact τ hτ

theorem surface_hausdorff (τ : ℂ) (hτ : 0<τ.im) : T2Space (Surface τ) := by
  letI : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  exact quotient_hausdorff (Periods τ)

theorem original_projection_holomorphic (τ : ℂ) (hτ : 0<τ.im) :
    letI := surfaceCharts τ hτ
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (projection (Periods τ)) := by
  letI : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  exact projection_contMDiff (Periods τ)

/-- Every element of the exact original integral quaternion order acts by a
holomorphic endomorphism of this same compact complex period surface. -/
theorem original_action_holomorphic (τ : ℂ) (hτ : 0<τ.im) (a : order) :
    letI := surfaceCharts τ hτ
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (orderEnd representation order τ a) := by
  letI : DiscreteTopology (Periods τ) := PELOriginalPeriodLattice318.original_discrete τ hτ
  exact descended_linear_contMDiff (Periods τ) (leftLinear (representation a))
    (orderEnd representation order τ a) (fun _ => rfl)
end PELComplexPeriodSurface318
