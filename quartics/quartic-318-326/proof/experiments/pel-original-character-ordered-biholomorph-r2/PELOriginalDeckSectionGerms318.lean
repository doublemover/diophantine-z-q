module
public import PELOriginalKernelStableOpens318
public import FourRootSchemeGenericDeck318
public section
noncomputable section
namespace PELOriginalDeckSectionGerms318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterPullback318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalKernelStableOpens318 PELOriginalGenericLabelsExhaustive318
open PELOriginalCharacterSectionInvariants318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
local instance sourceIntegral:IsIntegral Model:=
  FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance deckIso (g:Labels):IsIso (schemeDeck g):=by
  change IsIso (FourRootSchemeSignAction318.schemeIso branches (basis g)).hom
  infer_instance

/-- The same native sourceEquiv intertwines the ACTUAL scheme generic
pullback and the original label automorphism; not a newly chosen field iso. -/
lemma native_deck_square (g:Labels) (z:Model.functionField):
    sourceEquiv (DominantFunctionField318.map (schemeDeck g) z)=
      originalAutomorphism g (sourceEquiv z):=
  FourRootSchemeGenericDeck318.equivariant branches branches_injective (basis g) z

lemma originalGerm_sectionAction (i:Fin 4) (U:(Curve i).Opens)
    [Nonempty U] [Nonempty (morphism i⁻¹ᵁU)]
    (g:Labels) (hg:g∈(character i).ker) (x:Γ(Model,morphism i⁻¹ᵁU)):
    originalGerm i U (sectionAction i U g hg x)=
      originalAutomorphism g (originalGerm i U x):=by
  change sourceEquiv (Model.germToFunctionField _
    (StableOpenSectionPullback318.sectionPullback (schemeDeck g) _ _ x))=
    originalAutomorphism g (sourceEquiv (Model.germToFunctionField _ x))
  rw [StableOpenSectionPullback318.germ_sectionPullback,native_deck_square]

/-- Equality of original field germs is equivalent to equality of actual
regular sections, because this is the unchanged injective native germ. -/
lemma fixed_iff (i:Fin 4) (U:(Curve i).Opens)
    [Nonempty U] [Nonempty (morphism i⁻¹ᵁU)]
    (g:Labels) (hg:g∈(character i).ker) (x:Γ(Model,morphism i⁻¹ᵁU)):
    sectionAction i U g hg x=x ↔
      originalAutomorphism g (originalGerm i U x)=originalGerm i U x:=by
  constructor
  · intro h
    rw [←originalGerm_sectionAction,h]
  · intro h
    apply originalGerm_injective i U
    rw [originalGerm_sectionAction,h]
end PELOriginalDeckSectionGerms318
