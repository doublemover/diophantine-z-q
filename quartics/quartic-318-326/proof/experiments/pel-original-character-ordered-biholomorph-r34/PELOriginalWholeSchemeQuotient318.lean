module
public import PELOriginalArbitraryTargetGluing318
public section
noncomputable section
namespace PELOriginalWholeSchemeQuotient318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalArbitraryTargetGluing318
local instance mapFlat (i:Fin 4):Flat (morphism i):=PELOriginalWholeCharacterFlat318.flat i
local instance mapSurjective (i:Fin 4):Surjective (morphism i):=PELOriginalWholeCharacterProper318.surjective i

/-- Categorical quotient universal property for EVERY scheme target in
the same universe, for the SAME original whole character morphism and
original character kernel. All local maps, domains and overlaps are produced. -/
theorem existsUnique_factor {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
    (hg:∀a:Kernel i,schemeDeck a.val≫g=g):
    ∃!k:Curve i⟶Z,morphism i≫k=g:=by
  letI:Epi (morphism i):=Flat.epi_of_flat_of_surjective _
  refine ⟨quotientLift i g hg,quotientLift_factor i g hg,?_⟩
  intro k hk
  exact (cancel_epi (morphism i)).mp (hk.trans (quotientLift_factor i g hg).symm)

/-- Exact converse uses the original whole deck square; no quotient
assumption is fed back into the construction. -/
theorem factor_exists_iff {Z:Scheme} (i:Fin 4) (g:Model⟶Z):
    (∃k:Curve i⟶Z,morphism i≫k=g) ↔ ∀a:Kernel i,schemeDeck a.val≫g=g:=by
  constructor
  · rintro ⟨k,rfl⟩ a
    rw [←Category.assoc,PELOriginalWholeCharacterDeck318.whole_deck_square i a.val a.property]
  · intro hg
    obtain ⟨k,hk,_⟩:=existsUnique_factor i g hg
    exact ⟨k,hk⟩
end PELOriginalWholeSchemeQuotient318
