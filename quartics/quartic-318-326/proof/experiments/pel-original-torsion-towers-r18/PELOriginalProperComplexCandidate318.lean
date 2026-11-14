module
public import ComplexProjectiveBase318
public import PELOriginalCandidateComplexPoints318
public section
noncomputable section
namespace PELOriginalProperComplexCandidate318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318
open PELOriginalCandidateComplexPoints318 PELOriginalPolarizationTransitions318
variable (τ:ℂ)(hτ:0<τ.im)

/-- The same actual reduced closed candidate, now with its literal
complex structure morphism. Properness comes from actual polynomial
Proj properness and its genuine closed immersion, not analytic compactness. -/
@[expose] def structureMap:candidate τ hτ⟶ComplexProjectiveSchemePoint318.ComplexPoint:=
  inclusion τ hτ≫ComplexProjectiveBase318.structureMap
instance proper:IsProper (structureMap τ hτ):=by
  dsimp [structureMap]
  infer_instance
lemma inclusion_over:
    inclusion τ hτ≫ComplexProjectiveBase318.structureMap=structureMap τ hτ:=rfl

/-- Every constructed original complex-valued point lies OVER C with
identity base map. This uses the same literal polynomial constants,
not just an abstract set-point correspondence. -/
@[reassoc] theorem candidate_point_over(q:Base τ):
    candidateComplexPoint τ hτ q≫structureMap τ hτ=𝟙 _:=by
  rw [structureMap,←Category.assoc,candidateComplexPoint_inclusion]
  exact ComplexProjectiveBase318.point_over _ _
end PELOriginalProperComplexCandidate318

