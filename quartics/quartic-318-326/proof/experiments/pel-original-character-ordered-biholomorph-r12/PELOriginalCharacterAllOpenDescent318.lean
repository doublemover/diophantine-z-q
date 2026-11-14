module
public import PELOriginalCharacterInvariantSections318
public import InjectiveRingHomDescent318
public section
noncomputable section
namespace PELOriginalCharacterAllOpenDescent318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalCharacterAllOpenInvariants318
variable {T:Type*} [CommRing T]

/-- Every invariant test-ring map descends uniquely on EVERY target open;
empty opens and the whole proper target are included, without affineness. -/
theorem existsUnique_factor (i:Fin 4) (U:(Curve i).Opens)
    (f:T→+*Γ(Model,morphism i⁻¹ᵁU)) (hf:∀x:T,Invariant i U (f x)):
    ∃!k:T→+*Γ(Curve i,U),((morphism i).app U).hom.comp k=f:=by
  apply InjectiveRingHomDescent318.existsUnique_factor
    ((morphism i).app U).hom (app_injective i U) f
  intro x
  exact (range_iff i U (f x)).mpr (hf x)

/-- A global regular-section factorization on the SAME whole character
map. No global scheme quotient is inferred from global functions alone. -/
theorem global_existsUnique_factor (i:Fin 4)
    (f:T→+*Γ(Model,morphism i⁻¹ᵁ⊤)) (hf:∀x:T,Invariant i ⊤ (f x)):
    ∃!k:T→+*Γ(Curve i,⊤),((morphism i).app ⊤).hom.comp k=f:=
  existsUnique_factor i ⊤ f hf
end PELOriginalCharacterAllOpenDescent318
