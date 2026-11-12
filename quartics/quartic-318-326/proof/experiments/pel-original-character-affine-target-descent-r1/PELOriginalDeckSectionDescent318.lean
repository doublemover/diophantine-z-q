module
public import PELOriginalDeckFixedSections318
public section
noncomputable section
namespace PELOriginalDeckSectionDescent318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalDeckFixedSections318

/-- The image of the SAME whole character morphism on EVERY open is
exactly the sections fixed by all of its original scheme deck maps. -/
theorem range_iff_fixed (i:Fin 4) (U:(Curve i).Opens)
    (x:Γ(Model,morphism i⁻¹ᵁU)):
    x∈Set.range ((morphism i).app U).hom ↔ DeckFixed i U x:=by
  rw [PELOriginalCharacterAllOpenInvariants318.range_iff,invariant_iff_deckFixed]

/-- Unique test-ring descent now assumes actual scheme-section fixedness,
not generic-field invariance. The entire infinity inverse image is retained. -/
theorem existsUnique_factor {T:Type*} [CommRing T] (i:Fin 4) (U:(Curve i).Opens)
    (f:T→+*Γ(Model,morphism i⁻¹ᵁU)) (hf:∀x:T,DeckFixed i U (f x)):
    ∃!k:T→+*Γ(Curve i,U),((morphism i).app U).hom.comp k=f:=by
  apply PELOriginalCharacterAllOpenDescent318.existsUnique_factor i U f
  intro x
  exact (invariant_iff_deckFixed i U (f x)).mpr (hf x)

/-- Whole-source specialization of the actual section-action universal
property. Arbitrary-scheme target descent is NOT inferred from this alone. -/
theorem global_existsUnique_factor {T:Type*} [CommRing T] (i:Fin 4)
    (f:T→+*Γ(Model,morphism i⁻¹ᵁ⊤)) (hf:∀x:T,DeckFixed i ⊤ (f x)):
    ∃!k:T→+*Γ(Curve i,⊤),((morphism i).app ⊤).hom.comp k=f:=
  existsUnique_factor i ⊤ f hf
end PELOriginalDeckSectionDescent318
