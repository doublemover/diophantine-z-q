module
public import PELOriginalCompletedLegendreBijection318
public section
noncomputable section
namespace PELOriginalCharacterDeck318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalCompletedLegendreBijection318
open PELOriginalBranchLabels318 PELUnlevelledComplexBase318

lemma toggle_square (i:Fin 4) : toggle i*toggle i=1 := by
  change Multiplicative.ofAdd (fun j=>if j=i then (1:ZMod 2) else 0)*
    Multiplicative.ofAdd (fun j=>if j=i then (1:ZMod 2) else 0)=1
  change (fun j=>if j=i then (1:ZMod 2) else 0)+
    (fun j=>if j=i then (1:ZMod 2) else 0)=(0:Fin 4→ZMod 2)
  funext j
  by_cases h:j=i <;> simp [h]

/-- Descend the LITERAL original prime-character toggle, not an involution
transported from the proposed Legendre target. Commutativity of the actual
label group preserves the actual kernel-orbit equivalence relation. -/
@[expose] def deckMap (i:Fin 4) : CharacterBase i→CharacterBase i:=
  Quotient.map (fun x:UnlevelledBase=>toggle i • x) (by
    intro x y h
    obtain ⟨g,hg⟩:=h
    refine ⟨g,?_⟩
    change (g:Labels) • (toggle i • y)=toggle i • x
    rw [←hg,←mul_smul,←mul_smul,mul_comm])
lemma deckMap_original (i:Fin 4) (x:UnlevelledBase) :
    deckMap i (toCharacter i x)=toCharacter i (toggle i • x):=rfl
lemma deckMap_involutive (i:Fin 4) : Function.Involutive (deckMap i) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro a
  rw [deckMap_original,deckMap_original,←mul_smul,toggle_square,one_smul]
@[expose] def deck (i:Fin 4) : CharacterBase i≃CharacterBase i:=
  ⟨deckMap i,deckMap i,deckMap_involutive i,deckMap_involutive i⟩
lemma deck_projection (i:Fin 4) (x:CharacterBase i) : normalizedMap i (deck i x)=normalizedMap i x := by
  refine Quotient.inductionOn x ?_
  intro a
  apply congrArg (coordinate i)
  change PELOriginalMaximalQuotient318.projection (toggle i • a)=PELOriginalMaximalQuotient318.projection a
  exact (PELOriginalMaximalQuotient318.projection_eq_iff _ _).mpr ⟨toggle i,rfl⟩

/-- The actual original deck fixed locus is EXACTLY the four original
normalized branch fibers; this is derived from the full original fiber
pair and cardinality, not from an assumed cover identification. -/
theorem fixed_iff_branch (i:Fin 4) (x:CharacterBase i) :
    deck i x=x ↔ Branch i (normalizedMap i x) := by
  refine Quotient.inductionOn x ?_
  intro a
  have hc:=Nat.card_congr (fiberEquiv i (PELOriginalMaximalQuotient318.projection a))
  rw [fiber_card] at hc
  change Nat.card {y:CharacterBase i//normalizedMap i y=normalizedMap i (toCharacter i a)}=_ at hc
  rw [all_fibers] at hc
  change (if Branch i (normalizedMap i (toCharacter i a)) then 1 else 2)=
    if toCharacter i a=toCharacter i (toggle i • a) then 1 else 2 at hc
  change toCharacter i (toggle i • a)=toCharacter i a ↔ _
  by_cases hb:Branch i (normalizedMap i (toCharacter i a)) <;>
    by_cases he:toCharacter i a=toCharacter i (toggle i • a) <;>
    simp_all [eq_comm]

/-- Exact equivariance of the FIXED completed comparison with the actual
original deck action and the actual target sign action, including all
four branch points and infinity. This does not define the source deck
by transport through the comparison. -/
theorem completedMap_equivariant (i:Fin 4) (x:CharacterBase i) :
    completedMap i (deck i x)=NormalizedLegendreWholeProjection318.deck (branchParameter i) (completedMap i x) := by
  have hp:NormalizedLegendreWholeProjection318.coordinate (branchParameter i) (completedMap i x)=
      NormalizedLegendreWholeProjection318.coordinate (branchParameter i) (completedMap i (deck i x)):=by
    rw [completed_projection,completed_projection,deck_projection]
  by_cases hf:deck i x=x
  · have hb:Branch i (normalizedMap i x):=(fixed_iff_branch i x).mp hf
    have ht:= (NormalizedLegendreWholeProjection318.fixed_iff_branch (branchParameter i) (completedMap i x)).mpr
      ((completed_projection i x).symm ▸ hb)
    rw [hf,ht]
  · rcases (NormalizedLegendreWholeProjection318.same_coordinate (branchParameter i) _ _).mp hp with he|he
    · exact False.elim (hf ((completedMap_injective i he).symm))
    · exact he.symm
end PELOriginalCharacterDeck318
