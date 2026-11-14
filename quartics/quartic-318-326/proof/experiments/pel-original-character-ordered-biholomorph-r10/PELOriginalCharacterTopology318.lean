module
public import PELOriginalCharacterBranches318
public section
noncomputable section
namespace PELOriginalCharacterTopology318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalBaseCompact318

/-- All eight original words of the character kernel are retained. -/
lemma kernel_card : ∀ i : Fin 4, Fintype.card (character i).ker = 8 := by decide

lemma toCharacter_continuous (i : Fin 4) : Continuous (toCharacter i) := continuous_quot_mk
lemma toCharacter_open (i : Fin 4) : IsOpenMap (toCharacter i) :=
  isOpenMap_quotient_mk'_mul
lemma toCharacter_surjective (i : Fin 4) : Function.Surjective (toCharacter i) :=
  Quotient.mk_surjective

instance characterCompact (i : Fin 4) : CompactSpace (CharacterBase i) := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (toCharacter_surjective i), ← Set.image_univ]
  exact isCompact_univ.image (toCharacter_continuous i)
instance characterT2 (i : Fin 4) : T2Space (CharacterBase i) := inferInstance

lemma toMaximal_continuous (i : Fin 4) : Continuous (toMaximal i) :=
  PELOriginalMaximalQuotient318.projection_continuous.quotient_lift _

lemma toMaximal_surjective (i : Fin 4) : Function.Surjective (toMaximal i) := by
  intro q
  obtain ⟨x,rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
  exact ⟨toCharacter i x,rfl⟩

/-- These are actual compact Hausdorff intermediate quotients, with a proper
map to the SAME maximal quotient. Holomorphic charts, algebraization and the
published elliptic equations remain separate constructions. -/
lemma toMaximal_proper (i : Fin 4) : IsProperMap (toMaximal i) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨toMaximal_continuous i,?_,?_⟩
  · intro S hS
    exact (hS.isCompact.image (toMaximal_continuous i)).isClosed
  · intro q
    exact (isClosed_singleton.preimage (toMaximal_continuous i)).isCompact
end PELOriginalCharacterTopology318
