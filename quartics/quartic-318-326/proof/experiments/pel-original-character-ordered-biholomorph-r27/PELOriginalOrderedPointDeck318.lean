module
public import PELOriginalOrderedPointProjection318
public import PELOriginalCharacterDeck318
public section
noncomputable section
namespace PELOriginalOrderedPointDeck318
open AlgebraicGeometry CategoryTheory
open PELOriginalCharacterQuotient318 PELOriginalOrderedCharacterPointMap318
open PELOriginalCharacterDeck318 PELOriginalDescendedCharacterKernel318
open PELOriginalDescendedLabelMaps318

/-- The literal original analytic toggle is mapped to the SAME descended
scheme involution, not defined by transport through this point map. -/
theorem deck_square (i:Fin 4) (x:CharacterBase i):
    (pointMap i (deck i x)).val=(pointMap i x).val≫(residual i).hom:=by
  refine Quotient.inductionOn x ?_
  intro a
  change (sourceMap i (toggle i • a)).val=(sourceMap i a).val≫(residual i).hom
  rw [source_equivariant]
  change _=((PELOriginalContactSchemePoints318.comparison a).val≫
    PELOriginalWholeCharacterMorphisms318.morphism i)≫descended i (toggle i)
  rw [Category.assoc,descended_square]

lemma deck_base (i:Fin 4) (x:CharacterBase i):toMaximal i (deck i x)=toMaximal i x:=by
  refine Quotient.inductionOn x ?_
  intro a
  change PELOriginalMaximalQuotient318.projection (toggle i • a)=
    PELOriginalMaximalQuotient318.projection a
  exact (PELOriginalMaximalQuotient318.projection_eq_iff _ _).mpr ⟨toggle i,rfl⟩

/-- Full original double-cover fibers, with the actual original deck and
without assuming injectivity of the new ordered point map. -/
theorem same_base_pair (i:Fin 4) (x y:CharacterBase i):
    toMaximal i x=toMaximal i y ↔ x=y ∨ deck i x=y:=by
  constructor
  · refine Quotient.inductionOn x ?_
    intro a h
    have hy:y∈{z:CharacterBase i|toMaximal i z=PELOriginalMaximalQuotient318.projection a}:=h.symm
    rw [full_fiber_pair] at hy
    rcases hy with hy|hy
    · exact Or.inl hy.symm
    · exact Or.inr hy.symm
  · rintro (rfl|h)
    · rfl
    · rw [←h,deck_base]
end PELOriginalOrderedPointDeck318
