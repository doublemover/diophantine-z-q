module
public import PELPrincipalThreeCovering318
public import HolomorphicQuotientCoverMaps318
public section
noncomputable section
namespace PELPrincipalBaseHolomorphy318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicUnitPeriodTransport318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318 PELOriginalUnitBiholomorph318
open PELPrincipalThreeFreeAction318 PELPrincipalProperAction318 PELPrincipalThreeCovering318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000

theorem baseChart_source (τ : HalfPlane) : τ∈baseChart.source := Set.mem_univ _
theorem baseChart_value (τ : HalfPlane) : baseChart τ=(τ:ℂ) := rfl

@[expose,instance_reducible] def halfPlaneCharts : ChartedSpace ℂ HalfPlane where
  atlas := {baseChart}
  chartAt _ := baseChart
  mem_chart_source := baseChart_source
  chart_mem_atlas _ := Set.mem_singleton _

theorem halfPlane_manifold :
    letI := halfPlaneCharts
    IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := by
  letI := halfPlaneCharts
  apply isManifold_of_contDiffOn
  rintro e e' he he'
  have heq : e=baseChart := he
  have heq' : e'=baseChart := he'
  subst e
  subst e'
  have h : ContDiffOn ℂ ω (baseChart.symm.trans baseChart)
      (baseChart.symm.trans baseChart).source := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [baseChart.open_target.mem_nhds hz.1] with w hw
    exact baseChart.right_inv hw
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using h

local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold

theorem baseChart_maximal :
    baseChart∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω HalfPlane :=
  IsManifold.subset_maximalAtlas (Set.mem_singleton _)

theorem inclusion_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun τ : HalfPlane => (τ:ℂ)) :=
  fun τ => contMDiffAt_of_mem_maximalAtlas baseChart_maximal (baseChart_source τ)

/-- Holomorphy into the genuine open upper half-plane is recovered from
its original complex coordinate, via the actual open chart inverse. -/
theorem lift_holomorphic {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ,F) ω N]
    (f : N → HalfPlane)
    (hf : ContMDiff 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ω (fun x => (f x:ℂ))) :
    ContMDiff 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ω f := by
  intro x
  have ht : (f x:ℂ)∈baseChart.target := baseChart.map_source (baseChart_source (f x))
  have hi := contMDiffAt_symm_of_mem_maximalAtlas baseChart_maximal ht
  apply (hi.comp x (hf x)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => (baseChart.left_inv (baseChart_source (f y))).symm)

/-- The exact original principal-three action is holomorphic on the base
atlas, with the same denominator and the same positive upper-half-plane. -/
theorem principal_base_holomorphic (u : principalThree) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun τ : HalfPlane => u • τ) := by
  apply lift_holomorphic
  intro τ
  have hn : AnalyticAt ℂ (fun z : ℂ =>
      (unitMatrix representation order u.val 0 0:ℂ)*z+
        (unitMatrix representation order u.val 0 1:ℂ)) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hd : AnalyticAt ℂ (unitDenominator representation order u.val) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (unitParameter representation order u.val) (τ:ℂ) :=
    contMDiffAt_iff_contDiffAt.mpr
      (hn.div hd (denominator_nonzero u.val (determinant u) τ τ.property)).contDiffAt
  exact hm.comp τ (inclusion_holomorphic τ)

local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

/-- The same original joint projection now lands holomorphically in the
upper-half-plane manifold, not only in its ambient complex coordinate. -/
theorem original_projection_holomorphic :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,ℂ) ω (Prod.fst : Total → HalfPlane) :=
  lift_holomorphic Prod.fst PELHolomorphicFamilyProjection318.base_holomorphic
end PELPrincipalBaseHolomorphy318
