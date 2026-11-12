module
public import PELOriginalCharacterProjection318
public import Mathlib.Topology.Covering.Basic
public section
noncomputable section
namespace PELOriginalCharacterUnramifiedCover318
open Set Filter Topology
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalCharacterTopologicalAtlas318 PELOriginalCharacterBranches318
open PELOriginalBranchLabels318
variable (i:Fin 4)

/-- Openness is derived from the TWO actual quotient projections. -/
lemma toMaximal_open : IsOpenMap (toMaximal i) := by
  intro U hU
  have he:toMaximal i '' U=PELOriginalMaximalQuotient318.projection '' (toCharacter i ⁻¹' U) := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      obtain ⟨x,rfl⟩:=toCharacter_surjective i p
      exact ⟨x,hp,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨toCharacter i x,hx,rfl⟩
  rw [he]
  exact PELOriginalMaximalQuotient318.projection_open _
    (hU.preimage (toCharacter_continuous i))

/-- Identity in two ORIGINAL local charts yields a genuine injective open
neighborhood for the original character-to-maximal map. -/
lemma local_injective_identity (p:UnlevelledBase)
    (U V:Set UnlevelledBase) (hU:IsOpen U) (hV:IsOpen V) (hpU:p∈U) (hpV:p∈V)
    (e:OpenPartialHomeomorph (CharacterBase i) ℂ) (b:OpenPartialHomeomorph MaximalBase ℂ)
    (hes:e.source=toCharacter i '' U)
    (hval:∀x∈U∩V,b (PELOriginalMaximalQuotient318.projection x)=e (toCharacter i x)) :
    ∃W:Set (CharacterBase i),IsOpen W ∧ toCharacter i p∈W ∧ InjOn (toMaximal i) W := by
  refine ⟨toCharacter i '' (U∩V),toCharacter_open i _ (hU.inter hV),⟨p,⟨hpU,hpV⟩,rfl⟩,?_⟩
  rintro x ⟨a,ha,rfl⟩ y ⟨b',hb,rfl⟩ heq
  apply e.injOn
  · rw [hes]; exact ⟨a,ha.1,rfl⟩
  · rw [hes]; exact ⟨b',hb.1,rfl⟩
  · rw [←hval a ha,←hval b' hb]
    exact congrArg b heq

/-- Omitted inertia is retained: it is unramified for this character even
though its lift is ramified for the full sixteen-element quotient. -/
theorem local_injective_off_branch (q:CharacterBase i)
    (hq:toMaximal i q∉CharacterBranchValues i) :
    ∃W:Set (CharacterBase i),IsOpen W ∧ q∈W ∧ InjOn (toMaximal i) W := by
  obtain ⟨p,rfl⟩:=toCharacter_surjective i q
  by_cases hp:p∈nontrivialStabilizerLocus
  · obtain ⟨j,hj⟩:=(original_locus_union p).mp hp
    have hχ:InertiaLabels318.fiveLabels j i=0 := by
      by_contra hχ
      apply hq
      change Nat.card {y:CharacterBase i // toMaximal i y=PELOriginalMaximalQuotient318.projection p}=1
      exact (branch_fiber_card i j p hj).trans (if_neg hχ)
    obtain ⟨τ,rfl⟩:=PELUnlevelledComplexBase318.projection_surjective p
    obtain ⟨U,e,hU,hpU,hes,heval,_⟩:=
      PELOriginalCharacterOmittedSquare318.omitted_chart i j τ hj hχ
    obtain ⟨V,b,hV,hpV,_,hbval,_⟩:=
      PELMaximalTopologicalAtlas318.exists_branch_chart j τ hj
    apply local_injective_identity i _ U V hU hV hpU hpV e b hes
    intro x hx
    exact (hbval x hx.2).trans (heval x hx.1).symm
  · obtain ⟨U,e,hU,hpU,hes,heval,_⟩:=regular_chart i p hp
    obtain ⟨V,b,hV,hpV,_,hbval,_⟩:=PELRegularQuotientChart318.exists_regular_chart p hp
    apply local_injective_identity i p U V hU hV hpU hpV e b hes
    intro x hx
    exact (hbval x hx.2).trans (heval x hx.1).symm

/-- Compactness supplies evenly covered neighborhoods once the exact
regular AND omitted-inertia chart comparisons have been constructed. -/
theorem covering_off_branch : IsCoveringMapOn (toMaximal i) (CharacterBranchValues i)ᶜ := by
  apply IsCoveringMapOn.of_isLocalHomeomorphOn (toMaximal_continuous i)
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro q hq
  obtain ⟨W,hW,hqW,hinj⟩:=local_injective_off_branch i q hq
  refine ⟨W,hW.mem_nhds hqW,?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨(toMaximal_continuous i).comp continuous_subtype_val,
    Set.injOn_iff_injective.mp hinj,(toMaximal_open i).comp hW.isOpenMap_subtype_val⟩
end PELOriginalCharacterUnramifiedCover318
