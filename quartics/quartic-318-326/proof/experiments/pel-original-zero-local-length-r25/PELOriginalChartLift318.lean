module
public import PELMaximalTopologicalAtlas318
public section
noncomputable section
namespace PELOriginalChartLift318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- The original quotient projection is invariant under every element
of the actual sixteen-element normalizer action. -/
theorem projection_action (g : Labels) (p : UnlevelledBase) :
    PELOriginalMaximalQuotient318.projection (g • p)=
      PELOriginalMaximalQuotient318.projection p :=
  (PELOriginalMaximalQuotient318.projection_eq_iff _ _).mpr ⟨g,rfl⟩

/-- Retained analytic chart evidence extends to EVERY original
representative over the full chart source, by the actual holomorphic action. -/
theorem lift_holomorphic (e : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart e) (p : UnlevelledBase)
    (hp : PELOriginalMaximalQuotient318.projection p∈e.source) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (PELOriginalMaximalQuotient318.projection y)) p := by
  obtain ⟨U,hU,hs,hhol⟩ := he
  rw [hs] at hp
  obtain ⟨x,hx,hqx⟩ := hp
  obtain ⟨g,hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff x p).mp hqx
  have hact := PELOriginalElementaryAction318.original_action_holomorphic g
  have hxhol : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (PELOriginalMaximalQuotient318.projection y)) (g • p) := by
    rw [hg]
    exact hhol x hx
  have h := hxhol.comp p hact.contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [] with y
  exact congrArg e (projection_action g y).symm
end PELOriginalChartLift318
