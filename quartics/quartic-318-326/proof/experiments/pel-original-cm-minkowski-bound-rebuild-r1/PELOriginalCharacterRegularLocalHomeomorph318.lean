module
public import PELOriginalOrderedRegularHolomorphy318
public section
noncomputable section
namespace PELOriginalCharacterRegularLocalHomeomorph318
open Set Topology
open scoped Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318
open PELOriginalCharacterTopology318 PELOriginalContactRootFunctions318
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold

/-- The original kernel quotient is a local homeomorphism on the actual
full regular locus, derived from its genuine free-action charts. -/
theorem local_homeomorph (i:Fin 4):IsLocalHomeomorphOn (toCharacter i) RegularSource:=by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro p hp
  have hn:p∉PELOriginalBranchLabels318.nontrivialStabilizerLocus:=by
    intro h
    exact PELOriginalCompletedContactPoints318.not_regular_of_ramified p h hp
  obtain ⟨U,e,hU,hpU,_,hsub,_,hval⟩:=
    PELOriginalCharacterLocalSquare318.free_chart i p (chartAt ℂ p)
      (mem_chart_source ℂ p) Set.univ isOpen_univ (Set.mem_univ p)
      (PELOriginalCharacterTopologicalAtlas318.regular_kernel_free i p hn)
  have hinj:Set.InjOn (toCharacter i) U:=by
    intro x hx y hy hxy
    apply (chartAt ℂ p).injOn (hsub hx) (hsub hy)
    rw [←hval x hx,←hval y hy,hxy]
  refine ⟨U,hU.mem_nhds hpU,?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨(toCharacter_continuous i).comp continuous_subtype_val,
    Set.injOn_iff_injective.mp hinj,(toCharacter_open i).comp hU.isOpenMap_subtype_val⟩
end PELOriginalCharacterRegularLocalHomeomorph318
