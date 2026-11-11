module
public import PELRegularQuotientChart318
public section
noncomputable section
namespace PELMaximalTopologicalAtlas318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELDescendedInertiaChart318 PELInertiaSquaredCoordinate318
open PELRegularQuotientChart318 OpenImageHomeomorphChart318
open scoped Manifold ContDiff
open Filter Topology
set_option maxHeartbeats 1800000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- The descended branch homeomorphism is an actual ambient partial chart
with its exact squared original projection formula on every representative. -/
theorem exists_branch_chart (i : Fin 5) (τ : HalfPlane)
    (hp : PELUnlevelledComplexBase318.projection τ∈fixedLocus i) :
    ∃ (U : Set UnlevelledBase) (e : OpenPartialHomeomorph MaximalBase ℂ),
      IsOpen U ∧ PELUnlevelledComplexBase318.projection τ∈U ∧
      e.source=PELOriginalMaximalQuotient318.projection '' U ∧
      (∀ x∈U,e (PELOriginalMaximalQuotient318.projection x)=squaredCoordinate τ x) ∧
      ∀ x∈U,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
        (fun y => e (PELOriginalMaximalQuotient318.projection y)) x := by
  obtain ⟨U,hU,hpU,hsub,hfib⟩ :=
    PELMaximalSquaredLocalFibers318.original_squared_quotient_fibers i τ hp
  let E := descendedChart τ U hU hsub hfib
  have hQ := source_open U hU
  have hF := target_open τ U hU hsub
  let hne : Nonempty (PELOriginalMaximalQuotient318.projection '' U) :=
    ⟨⟨PELOriginalMaximalQuotient318.projection (PELUnlevelledComplexBase318.projection τ),
      ⟨PELUnlevelledComplexBase318.projection τ,hpU,rfl⟩⟩⟩
  let e := extend _ _ hQ hF hne E
  have hval : ∀ x∈U,e (PELOriginalMaximalQuotient318.projection x)=squaredCoordinate τ x := by
    intro x hx
    have he := extend_value _ _ hQ hF hne E
      (⟨PELOriginalMaximalQuotient318.projection x,⟨x,hx,rfl⟩⟩:
        PELOriginalMaximalQuotient318.projection '' U)
    exact he.trans (descended_value τ U hU hsub hfib x hx)
  refine ⟨U,e,hU,hpU,extend_source _ _ hQ hF hne E,hval,?_⟩
  intro x hx
  have hs : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (squaredCoordinate τ) x :=
    (chart_holomorphic τ x (hsub hx)).pow 2
  apply hs.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hval y hy

/-- Retained construction evidence for every chosen chart: its full source
is the quotient image of an actual open domain where its original projection
lift is holomorphic. This survives the choice of the topological atlas. -/
@[expose] def OriginalChart (e : OpenPartialHomeomorph MaximalBase ℂ) : Prop :=
  ∃ U : Set UnlevelledBase,IsOpen U ∧ e.source=PELOriginalMaximalQuotient318.projection '' U ∧
    ∀ x∈U,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (PELOriginalMaximalQuotient318.projection y)) x

/-- Every point of the LITERAL full-normalizer quotient has a complex-
plane-modeled topological chart. The regular and branch constructions use
actual original points, so there is no uncovered exceptional locus. -/
theorem exists_chart (q : MaximalBase) :
    ∃ e : OpenPartialHomeomorph MaximalBase ℂ,q∈e.source ∧ OriginalChart e := by
  obtain ⟨p,rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
  by_cases hp : p∈nontrivialStabilizerLocus
  · obtain ⟨i,hi⟩ := (original_locus_union p).mp hp
    obtain ⟨τ,rfl⟩ := PELUnlevelledComplexBase318.projection_surjective p
    obtain ⟨U,e,hU,hpU,hs,he,hhol⟩ := exists_branch_chart i τ hi
    refine ⟨e,?_,U,hU,hs,hhol⟩
    rw [hs]
    exact ⟨PELUnlevelledComplexBase318.projection τ,hpU,rfl⟩
  · obtain ⟨U,e,hU,hpU,hs,he,hhol⟩ := exists_regular_chart p hp
    refine ⟨e,?_,U,hU,hs,hhol⟩
    rw [hs]
    exact ⟨p,hpU,rfl⟩

@[expose] def chosenChart (q : MaximalBase) : OpenPartialHomeomorph MaximalBase ℂ :=
  Classical.choose (exists_chart q)

theorem chosenChart_center (q : MaximalBase) : q∈(chosenChart q).source :=
  (Classical.choose_spec (exists_chart q)).1

theorem chosenChart_original (q : MaximalBase) : OriginalChart (chosenChart q) :=
  (Classical.choose_spec (exists_chart q)).2

/-- A genuine full topological atlas on the original quotient topology.
Holomorphic transition maps and IsManifold are NOT asserted here. -/
@[expose,instance_reducible] def maximalTopologicalCharts : ChartedSpace ℂ MaximalBase where
  atlas := Set.range chosenChart
  chartAt := chosenChart
  mem_chart_source := chosenChart_center
  chart_mem_atlas q := ⟨q,rfl⟩
end PELMaximalTopologicalAtlas318
