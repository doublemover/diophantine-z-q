module
public import PELOriginalCharacterOmittedSquare318
public section
noncomputable section
namespace PELOriginalCharacterTopologicalAtlas318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318
open PELOriginalCharacterLocalSquare318 PELOriginalCharacterOmittedSquare318
open PELOriginalBranchLabels318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

lemma regular_kernel_free (i : Fin 4) (p : UnlevelledBase)
    (hp : p ∉ nontrivialStabilizerLocus)
    (k : (character i).ker) (hk : k • p = p) : k = 1 := by
  apply Subtype.ext
  by_contra hne
  apply hp
  refine ⟨Multiplicative.toAdd (k : PELOriginalMaximalQuotient318.Labels),?_,hk⟩
  intro hz
  exact hne (congrArg Multiplicative.ofAdd hz)

/-- Ordinary source coordinates descend at every regular original point. -/
theorem regular_chart (i : Fin 4) (p : UnlevelledBase)
    (hp : p ∉ nontrivialStabilizerLocus) :
    ∃ (U : Set UnlevelledBase) (e : OpenPartialHomeomorph (CharacterBase i) ℂ),
      IsOpen U ∧ p ∈ U ∧ e.source = toCharacter i '' U ∧
      (∀ x ∈ U,e (toCharacter i x) = chartAt ℂ p x) ∧
      ∀ x ∈ U,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
        (fun y => e (toCharacter i y)) x := by
  obtain ⟨U,e,hU,hpU,_,hsub,hes,heval⟩ := free_chart i p (chartAt ℂ p)
    (mem_chart_source ℂ p) Set.univ isOpen_univ (Set.mem_univ p) (regular_kernel_free i p hp)
  refine ⟨U,e,hU,hpU,hes,heval,?_⟩
  intro x hx
  have hh := contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) (hsub hx)
  apply hh.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact heval y hy

/-- The original representative-domain and holomorphic lift are retained
for EVERY actual intermediate quotient chart. -/
@[expose] def OriginalChart (i : Fin 4)
    (e : OpenPartialHomeomorph (CharacterBase i) ℂ) : Prop :=
  ∃ U : Set UnlevelledBase,IsOpen U ∧ e.source = toCharacter i '' U ∧
    ∀ x ∈ U,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => e (toCharacter i y)) x

/-- All points of each actual intermediate quotient are covered. The
original inertia label is either visible or omitted; neither exceptional
case is dropped, and no genus bound or RH premise enters this construction. -/
theorem exists_chart (i : Fin 4) (q : CharacterBase i) :
    ∃ e : OpenPartialHomeomorph (CharacterBase i) ℂ,q ∈ e.source ∧ OriginalChart i e := by
  obtain ⟨p,rfl⟩ := PELOriginalCharacterTopology318.toCharacter_surjective i q
  by_cases hp : p ∈ nontrivialStabilizerLocus
  · obtain ⟨j,hj⟩ := (original_locus_union p).mp hp
    obtain ⟨τ,rfl⟩ := PELUnlevelledComplexBase318.projection_surjective p
    by_cases hχ : InertiaLabels318.fiveLabels j i = 0
    · obtain ⟨U,e,hU,hpU,hs,hv,hh⟩ := omitted_chart i j τ hj hχ
      refine ⟨e,?_,U,hU,hs,hh⟩
      rw [hs]
      exact ⟨_,hpU,rfl⟩
    · obtain ⟨U,e,b,hU,hpU,hs,hb,hzero,hmodel,hh⟩ := visible_local_square i j τ hj hχ
      refine ⟨e,?_,U,hU,hs,hh⟩
      rw [hs]
      exact ⟨_,hpU,rfl⟩
  · obtain ⟨U,e,hU,hpU,hs,hv,hh⟩ := regular_chart i p hp
    refine ⟨e,?_,U,hU,hs,hh⟩
    rw [hs]
    exact ⟨_,hpU,rfl⟩

@[expose] def chosenChart (i : Fin 4) (q : CharacterBase i) :
    OpenPartialHomeomorph (CharacterBase i) ℂ := Classical.choose (exists_chart i q)
lemma chosenChart_center (i : Fin 4) (q : CharacterBase i) :
    q ∈ (chosenChart i q).source := (Classical.choose_spec (exists_chart i q)).1
lemma chosenChart_original (i : Fin 4) (q : CharacterBase i) :
    OriginalChart i (chosenChart i q) := (Classical.choose_spec (exists_chart i q)).2

/-- Full complex-plane-modeled topological atlas on the unchanged quotient
space. Holomorphic transitions are the next separate theorem. -/
@[expose,instance_reducible] def characterTopologicalCharts (i : Fin 4) :
    ChartedSpace ℂ (CharacterBase i) where
  atlas := Set.range (chosenChart i)
  chartAt := chosenChart i
  mem_chart_source := chosenChart_center i
  chart_mem_atlas q := ⟨q,rfl⟩
end PELOriginalCharacterTopologicalAtlas318
