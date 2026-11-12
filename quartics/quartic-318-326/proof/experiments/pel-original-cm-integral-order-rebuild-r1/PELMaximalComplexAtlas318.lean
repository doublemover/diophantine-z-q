module
public import PELMaximalTransitionHolomorphy318
public section
noncomputable section
namespace PELMaximalComplexAtlas318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318
open PELOriginalChartLift318 PELMaximalTransitionHolomorphy318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1700000
local instance : ChartedSpace ℂ QuaternionicJointPeriodTopology318.HalfPlane :=
  PELPrincipalBaseHolomorphy318.halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω QuaternionicJointPeriodTopology318.HalfPlane :=
  PELPrincipalBaseHolomorphy318.halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- A genuine Riemann-surface atlas on the literal full positive-
normalizer quotient, using EXACTLY the preceding topological charts.
This does not assert compactness, genus, algebraization or a canonical
PEL/contact-curve comparison. -/
theorem maximal_manifold :
    letI := maximalTopologicalCharts
    IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := by
  letI := maximalTopologicalCharts
  apply isManifold_of_contDiffOn
  rintro e f ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (transition_analyticOn (chosenChart a) (chosenChart b)
      (chosenChart_original a) (chosenChart_original b)).contDiffOn
      ((chosenChart a).symm.trans (chosenChart b)).open_source.uniqueDiffOn

local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold

/-- The original full quotient map is holomorphic at EVERY original
point, including every nontrivial stabilizer center. -/
theorem maximal_projection_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
    PELOriginalMaximalQuotient318.projection := by
  intro p
  let e := chosenChart (PELOriginalMaximalQuotient318.projection p)
  have hp : PELOriginalMaximalQuotient318.projection p∈e.source := chosenChart_center _
  have he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase :=
    IsManifold.subset_maximalAtlas ⟨PELOriginalMaximalQuotient318.projection p,rfl⟩
  have hL := lift_holomorphic e (chosenChart_original _) p hp
  have hI := contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)
  apply (hI.comp p hL).congr_of_eventuallyEq
  filter_upwards [PELOriginalMaximalQuotient318.projection_continuous.continuousAt.tendsto.eventually
    (e.open_source.mem_nhds hp)] with x hx
  exact (e.left_inv hx).symm

/-- The same upper-half-plane parameter reaches the full quotient by a
holomorphic map through the original norm-one base, without changing its
orbit relation or chosen topology. -/
theorem upper_projection_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
    (PELOriginalMaximalQuotient318.projection ∘ PELUnlevelledComplexBase318.projection) := by
  exact maximal_projection_holomorphic.comp PELUnlevelledComplexBase318.projection_holomorphic
end PELMaximalComplexAtlas318
