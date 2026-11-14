module
public import AffineTargetSchemeDescent318
public import PELOriginalDeckSectionDescent318
public section
noncomputable section
namespace PELOriginalAffineTargetInvariance318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 PELOriginalDeckFixedSections318
open AffineTargetCoordinates318

lemma sectionAction_top (i:Fin 4) (g:Labels) (hg:g∈(character i).ker):
    sectionAction i ⊤ g hg=(schemeDeck g).appTop.hom:=by
  ext x
  change Model.presheaf.map (homOfLE _).op ((schemeDeck g).appTop x)=_
  simp

/-- An actual scheme map to Spec R is invariant under the original
kernel iff its actual global-coordinate sections are deck-fixed. -/
theorem invariant_iff_coordinates {R:Type} [CommRing R] (i:Fin 4)
    (g:Model⟶Spec (CommRingCat.of R)):
    (∀(a:Labels),a∈(character i).ker → schemeDeck a≫g=g) ↔
      ∀r:R,DeckFixed i ⊤ (coordinates g r):=by
  constructor
  · intro hg r a ha
    have he:=congrArg coordinates (hg a ha)
    rw [coordinates_comp] at he
    rw [sectionAction_top]
    exact RingHom.congr_fun he r
  · intro hg a ha
    apply coordinates_injective
    rw [coordinates_comp]
    apply RingHom.ext
    intro r
    have he:=hg r a ha
    rw [sectionAction_top] at he
    exact he
end PELOriginalAffineTargetInvariance318
