module
public import PELOriginalAffineTargetInvariance318
public section
noncomputable section
namespace PELOriginalAffineTargetSchemeDescent318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open PELOriginalKernelStableOpens318 AffineTargetCoordinates318

/-- Categorical quotient property for EVERY affine target Spec R,
for the SAME original whole character morphism and original label kernel.
No generic map, pointwise factorization or substitute scheme is used. -/
theorem existsUnique_factor {R:Type} [CommRing R] (i:Fin 4)
    (g:Model⟶Spec (CommRingCat.of R))
    (hg:∀a:Labels,a∈(character i).ker → schemeDeck a≫g=g):
    ∃!k:Curve i⟶Spec (CommRingCat.of R),morphism i≫k=g:=by
  apply AffineTargetSchemeDescent318.existsUnique_factor (morphism i) g
  exact PELOriginalDeckSectionDescent318.global_existsUnique_factor i (coordinates g)
    ((PELOriginalAffineTargetInvariance318.invariant_iff_coordinates i g).mp hg)

/-- The converse is the unchanged original whole deck square, so this
is an exact existence criterion, not merely one-way invariant descent. -/
theorem factor_exists_iff {R:Type} [CommRing R] (i:Fin 4)
    (g:Model⟶Spec (CommRingCat.of R)):
    (∃k:Curve i⟶Spec (CommRingCat.of R),morphism i≫k=g) ↔
      ∀a:Labels,a∈(character i).ker → schemeDeck a≫g=g:=by
  constructor
  · rintro ⟨k,rfl⟩ a ha
    rw [←Category.assoc,PELOriginalWholeCharacterDeck318.whole_deck_square i a ha]
  · intro hg
    obtain ⟨k,hk,_⟩:=existsUnique_factor i g hg
    exact ⟨k,hk⟩
end PELOriginalAffineTargetSchemeDescent318
