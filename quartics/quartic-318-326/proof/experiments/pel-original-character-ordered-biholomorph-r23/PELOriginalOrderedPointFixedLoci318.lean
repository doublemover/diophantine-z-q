module
public import PELOriginalOrderedPointDeck318
public section
noncomputable section
namespace PELOriginalOrderedPointFixedLoci318
open AlgebraicGeometry CategoryTheory
open PELOriginalCharacterQuotient318 PELOriginalOrderedCharacterPointMap318
open PELOriginalOrderedCharacterCoordinate318 PELOriginalOrderedPointProjection318
open PELOriginalCharacterDeck318 PELOriginalDescendedCharacterKernel318
open NormalizedLegendreFieldPoints318 NormalizedLegendreFiniteProjection318
open ProjectiveLineComplexSchemePoints318
open scoped OnePoint

@[expose] def Branch (i:Fin 4) (z:OnePoint ℂ):Prop:=
  z=∞ ∨ z=(0:ℂ) ∨ z=(1:ℂ) ∨ z=(parameter i:ℂ)

lemma original_fixed (i:Fin 4) (x:CharacterBase i):
    deck i x=x ↔ Branch i (normalizedMap i x):=by
  have ho:=PELOriginalFourBranchCoordinate318.actual_branch_values i (toMaximal i x)
  have hn:=PELOriginalOrderedCharacterCoordinate318.actual_branch_values i (toMaximal i x)
  exact (PELOriginalCharacterDeck318.fixed_iff_branch i x).trans (ho.symm.trans hn)

/-- Exact target fixed locus for ALL Scheme-valued complex points, using
the full independent completed point equivalence, not only finite ones. -/
lemma target_fixed (i:Fin 4) (p:Points i):
    p.val≫(residual i).hom=p.val ↔
      project (parameter i) p=spherePoint ∞ ∨
      project (parameter i) p=spherePoint (0:ℂ) ∨
      project (parameter i) p=spherePoint (1:ℂ) ∨
      project (parameter i) p=spherePoint (parameter i:ℂ):=by
  obtain ⟨q,rfl⟩:=(schemeEquiv (parameter i)).surjective p
  rw [PELOriginalResidualBranchPoints318.residual_fixed_iff_branch]
  simp only [NormalizedLegendreWholeProjection318.whole_projection,
    spherePoint_bijective.1.eq_iff]

/-- Fixedness is REFLECTED as well as preserved before any point-map
injectivity is used. This prevents a collapse of the two regular sheets. -/
theorem reflects_fixed (i:Fin 4) (x:CharacterBase i):
    (pointMap i x).val≫(residual i).hom=(pointMap i x).val ↔ deck i x=x:=by
  rw [target_fixed,projection_square,original_fixed]
  simp only [Branch,spherePoint_bijective.1.eq_iff]
end PELOriginalOrderedPointFixedLoci318
