module
public import PELOriginalCharacterCharts318
public import PELOriginalMaximalCharts318
public section
noncomputable section
namespace PELOriginalCharacterProjection318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalCharacterTopologicalAtlas318 PELOriginalCharacterComplexAtlas318
open PELOriginalBranchLabels318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1700000
variable (i : Fin 4)
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
local instance : ChartedSpace ℂ (CharacterBase i) := characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := character_manifold i
local instance : ChartedSpace ℂ MaximalBase := PELMaximalTopologicalAtlas318.maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := PELMaximalComplexAtlas318.maximal_manifold

/-- A shared original local coordinate proves holomorphy of the ACTUAL
intermediate map, using the full quotient image of the common open domain. -/
lemma holomorphic_identity (p : UnlevelledBase)
    (U V : Set UnlevelledBase) (hU : IsOpen U) (hV : IsOpen V)
    (hpU : p ∈ U) (hpV : p ∈ V)
    (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (b : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart i e) (hb : PELMaximalTopologicalAtlas318.OriginalChart b)
    (hes : e.source = toCharacter i '' U)
    (hbs : b.source = PELOriginalMaximalQuotient318.projection '' V)
    (hval : ∀ x ∈ U ∩ V,
      b (PELOriginalMaximalQuotient318.projection x) = e (toCharacter i x)) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toMaximal i) (toCharacter i p) := by
  have hpE : toCharacter i p ∈ e.source := by rw [hes]; exact ⟨p,hpU,rfl⟩
  have hpB : PELOriginalMaximalQuotient318.projection p ∈ b.source := by
    rw [hbs]; exact ⟨p,hpV,rfl⟩
  have hzB : e (toCharacter i p) ∈ b.target := by
    rw [← hval p ⟨hpU,hpV⟩]
    exact b.map_source hpB
  have hE := PELOriginalCharacterCharts318.original_chart_holomorphic i e he _ hpE
  have hB := PELOriginalMaximalCharts318.original_inverse_holomorphic b hb _ hzB
  apply (hB.comp _ hE).congr_of_eventuallyEq
  have hn : toCharacter i '' (U ∩ V) ∈ 𝓝 (toCharacter i p) :=
    (toCharacter_open i _ (hU.inter hV)).mem_nhds ⟨p,⟨hpU,hpV⟩,rfl⟩
  filter_upwards [hn] with q hq
  obtain ⟨x,hx,rfl⟩ := hq
  have hxB : PELOriginalMaximalQuotient318.projection x ∈ b.source := by
    rw [hbs]; exact ⟨x,hx.2,rfl⟩
  exact (b.left_inv hxB).symm.trans (congrArg b.symm (hval x hx))

/-- At visible inertia the established original local z² model is
holomorphic for BOTH exact constructed atlases. -/
lemma holomorphic_square (q : CharacterBase i)
    (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (b : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart i e) (hb : PELMaximalTopologicalAtlas318.OriginalChart b)
    (hqe : q ∈ e.source)
    (hmodel : ∀ y ∈ e.source,toMaximal i y ∈ b.source ∧
      b (toMaximal i y) = (e y)^2) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toMaximal i) q := by
  have hqB := (hmodel q hqe).1
  have hzB : (e q)^2 ∈ b.target := by
    rw [← (hmodel q hqe).2]
    exact b.map_source hqB
  have hE := (PELOriginalCharacterCharts318.original_chart_holomorphic i e he q hqe).pow 2
  have hB := PELOriginalMaximalCharts318.original_inverse_holomorphic b hb _ hzB
  apply (hB.comp q hE).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hqe] with y hy
  exact (b.left_inv (hmodel y hy).1).symm.trans (congrArg b.symm (hmodel y hy).2)

/-- The SAME proper intermediate-to-maximal projection is holomorphic
EVERYWHERE: regular points, visible inertia, and omitted inertia. No source
genus/RH, algebraization, or published-model identity is assumed. -/
theorem toMaximal_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toMaximal i) := by
  intro q
  obtain ⟨p,rfl⟩ := toCharacter_surjective i q
  by_cases hp : p ∈ nontrivialStabilizerLocus
  · obtain ⟨j,hj⟩ := (original_locus_union p).mp hp
    obtain ⟨τ,rfl⟩ := PELUnlevelledComplexBase318.projection_surjective p
    by_cases hχ : InertiaLabels318.fiveLabels j i = 0
    · obtain ⟨U,e,hU,hpU,hes,heval,hehol⟩ :=
        PELOriginalCharacterOmittedSquare318.omitted_chart i j τ hj hχ
      obtain ⟨V,b,hV,hpV,hbs,hbval,hbhol⟩ :=
        PELMaximalTopologicalAtlas318.exists_branch_chart j τ hj
      apply holomorphic_identity i _ U V hU hV hpU hpV e b
        ⟨U,hU,hes,hehol⟩ ⟨V,hV,hbs,hbhol⟩ hes hbs
      intro x hx
      exact (hbval x hx.2).trans (heval x hx.1).symm
    · obtain ⟨U,e,b,hU,hpU,hes,hb,hzero,hmodel,hehol⟩ :=
        PELOriginalCharacterLocalSquare318.visible_local_square i j τ hj hχ
      apply holomorphic_square i _ e b ⟨U,hU,hes,hehol⟩ hb _ hmodel
      rw [hes]
      exact ⟨_,hpU,rfl⟩
  · obtain ⟨U,e,hU,hpU,hes,heval,hehol⟩ := regular_chart i p hp
    obtain ⟨V,b,hV,hpV,hbs,hbval,hbhol⟩ :=
      PELRegularQuotientChart318.exists_regular_chart p hp
    apply holomorphic_identity i p U V hU hV hpU hpV e b
      ⟨U,hU,hes,hehol⟩ ⟨V,hV,hbs,hbhol⟩ hes hbs
    intro x hx
    exact (hbval x hx.2).trans (heval x hx.1).symm
end PELOriginalCharacterProjection318
