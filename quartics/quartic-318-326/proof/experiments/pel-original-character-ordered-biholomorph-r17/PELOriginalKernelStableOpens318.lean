module
public import StableOpenSectionPullback318
public import PELOriginalCharacterInvariantPresheaf318
public import PELOriginalWholeCharacterDeck318
public section
noncomputable section
namespace PELOriginalKernelStableOpens318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterPullback318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
local instance sourceIntegral:IsIntegral Model:=
  FourRootWholeSchemeGeometry318.integral branches branches_injective

abbrev schemeDeck (g:Labels):Model⟶Model:=
  FourRootSchemeSignAction318.action branches (basis g)
local instance deckIso (g:Labels):IsIso (schemeDeck g):=by
  change IsIso (FourRootSchemeSignAction318.schemeIso branches (basis g)).hom
  infer_instance

/-- The full inverse image of EVERY target open is stable under each
original kernel label. This is a scheme-map equality, not a point census. -/
lemma preimage_stable (i:Fin 4) (U:(Curve i).Opens)
    (g:Labels) (hg:g∈(character i).ker):
    schemeDeck g⁻¹ᵁ(morphism i⁻¹ᵁU)=morphism i⁻¹ᵁU:=by
  rw [←Scheme.Hom.comp_preimage]
  rw [PELOriginalWholeCharacterDeck318.whole_deck_square i g hg]

/-- The ACTUAL scheme action on sections of the full inverse image,
including the entire infinity inverse image and empty opens. -/
@[expose] def sectionAction (i:Fin 4) (U:(Curve i).Opens)
    (g:Labels) (hg:g∈(character i).ker):
    Γ(Model,morphism i⁻¹ᵁU)→+*Γ(Model,morphism i⁻¹ᵁU):=
  StableOpenSectionPullback318.sectionPullback (schemeDeck g) _
    (preimage_stable i U g hg).ge

lemma restriction_square (i:Fin 4) {U V:(Curve i).Opens} (j:U⟶V)
    (g:Labels) (hg:g∈(character i).ker) (x:Γ(Model,morphism i⁻¹ᵁV)):
    sectionAction i U g hg
      (Model.presheaf.map (homOfLE ((morphism i).preimage_mono j.le)).op x)=
    Model.presheaf.map (homOfLE ((morphism i).preimage_mono j.le)).op
      (sectionAction i V g hg x):=
  StableOpenSectionPullback318.restriction_square (schemeDeck g) _ _ _ x
end PELOriginalKernelStableOpens318
