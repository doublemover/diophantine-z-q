module
public import PELOriginalOrderedPointFixedLoci318
public section
noncomputable section
namespace PELOriginalOrderedCharacterPointEquivalence318
open AlgebraicGeometry CategoryTheory
open PELOriginalCharacterQuotient318 PELOriginalOrderedCharacterPointMap318
open PELOriginalOrderedCharacterCoordinate318 PELOriginalOrderedPointProjection318
open PELOriginalOrderedPointDeck318 PELOriginalOrderedPointFixedLoci318
open PELOriginalCharacterDeck318
open NormalizedLegendreFiniteProjection318 ProjectiveLineComplexSchemePoints318

/-- Injectivity uses the exact original two-sheet fiber relation and the
REFLECTION of deck fixedness. It is not deduced from matching counts. -/
theorem injective (i:Fin 4):Function.Injective (pointMap i):=by
  intro x y h
  rcases (same_base_pair i x y).mp (same_base i h) with he|he
  · exact he
  · have hf:(pointMap i x).val≫(PELOriginalDescendedCharacterKernel318.residual i).hom=
        (pointMap i x).val:=by
      rw [←deck_square,he,h]
    have hx:deck i x=x:=(reflects_fixed i x).mp hf
    exact hx.symm.trans he

/-- Every target point is covered by one of the actual two original
sheets above its normalized coordinate, including the singleton branches. -/
theorem surjective (i:Fin 4):Function.Surjective (pointMap i):=by
  intro p
  obtain ⟨z,hz⟩:=spherePoint_bijective.2 (project (parameter i) p)
  obtain ⟨x,hx⟩:=normalized_surjective i z
  have hp:project (parameter i) (pointMap i x)=project (parameter i) p:=by
    rw [projection_square,hx,hz]
  rcases (PELOriginalResidualBranchPoints318.actual_projection_fiber i (pointMap i x) p).mp hp with h|h
  · exact ⟨x,h⟩
  · refine ⟨deck i x,Subtype.ext ?_⟩
    exact (deck_square i x).trans h

/-- Actual original analytic character quotient bijects with the full
base-preserving complex points of the FIXED ORDERED algebraic quotient.
This is a point equivalence; target-atlas continuity is a separate task. -/
@[expose] def equivalence (i:Fin 4):CharacterBase i≃Points i:=
  Equiv.ofBijective (pointMap i) ⟨injective i,surjective i⟩
lemma source_square (i:Fin 4) (x:PELUnlevelledComplexBase318.UnlevelledBase):
    (equivalence i (toCharacter i x)).val=
      (PELOriginalContactSchemePoints318.comparison x).val≫
        PELOriginalWholeCharacterMorphisms318.morphism i:=rfl
lemma projection (i:Fin 4) (x:CharacterBase i):
    project (parameter i) (equivalence i x)=spherePoint (normalizedMap i x):=
  projection_square i x
end PELOriginalOrderedCharacterPointEquivalence318
