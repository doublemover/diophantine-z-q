module
public import PELOriginalDeckSectionGerms318
public section
noncomputable section
namespace PELOriginalDeckFixedSections318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 PELOriginalCharacterAllOpenInvariants318
open PELOriginalCharacterInvariantSections318
local instance sourceIntegral:IsIntegral Model:=
  FourRootWholeSchemeGeometry318.integral
    PELOriginalCommonContactBase318.branches PELOriginalCommonContactBase318.branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (morphism i):=
  PELOriginalWholeCharacterProper318.dominant i

/-- Literal fixedness under the original glued scheme deck maps on
regular sections, rather than a predicate defined on a replacement field. -/
def DeckFixed (i:Fin 4) (U:(Curve i).Opens) (x:Γ(Model,morphism i⁻¹ᵁU)):Prop:=
  ∀(g:Labels) (hg:g∈(character i).ker),sectionAction i U g hg x=x

/-- The earlier generic-germ definition and ACTUAL section fixedness
coincide on every open, including empty opens. -/
theorem invariant_iff_deckFixed (i:Fin 4) (U:(Curve i).Opens)
    (x:Γ(Model,morphism i⁻¹ᵁU)):
    Invariant i U x ↔ DeckFixed i U x:=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:=DominantFunctionField318.preimage_nonempty (morphism i) U
    constructor
    · intro hx g hg
      exact (PELOriginalDeckSectionGerms318.fixed_iff i U g hg x).mpr (hx h g hg)
    · intro hx h' g hg
      exact (PELOriginalDeckSectionGerms318.fixed_iff i U g hg x).mp (hx g hg)
  · have hu:U=⊥:=by
      apply le_antisymm _ bot_le
      intro p hp
      exact (h ⟨⟨p,hp⟩⟩).elim
    haveI:Subsingleton Γ(Model,morphism i⁻¹ᵁU):=by
      rw [hu,Scheme.Hom.preimage_bot]
      infer_instance
    exact ⟨fun _ _ _=>Subsingleton.elim _ _,fun _ h'=>False.elim (h h')⟩

@[expose] def deckFixedSubring (i:Fin 4) (U:(Curve i).Opens):
    Subring Γ(Model,morphism i⁻¹ᵁU) where
  carrier:=DeckFixed i U
  zero_mem':=by intro g hg;exact (sectionAction i U g hg).map_zero
  one_mem':=by intro g hg;exact (sectionAction i U g hg).map_one
  add_mem':=by intro x y hx hy g hg;rw [map_add,hx g hg,hy g hg]
  mul_mem':=by intro x y hx hy g hg;rw [map_mul,hx g hg,hy g hg]
  neg_mem':=by intro x hx g hg;rw [map_neg,hx g hg]

/-- Equality of literal subrings inside the SAME full-inverse-image
section ring upgrades the all-open invariant-presheaf identification. -/
theorem subring_eq (i:Fin 4) (U:(Curve i).Opens):
    invariantSubring i U=deckFixedSubring i U:=by
  ext x
  exact invariant_iff_deckFixed i U x

lemma deckFixed_restrict (i:Fin 4) {U V:(Curve i).Opens} (j:U⟶V)
    (x:Γ(Model,morphism i⁻¹ᵁV)) (hx:DeckFixed i V x):
    DeckFixed i U
      (Model.presheaf.map (homOfLE ((morphism i).preimage_mono j.le)).op x):=by
  intro g hg
  rw [PELOriginalKernelStableOpens318.restriction_square,hx g hg]
end PELOriginalDeckFixedSections318
