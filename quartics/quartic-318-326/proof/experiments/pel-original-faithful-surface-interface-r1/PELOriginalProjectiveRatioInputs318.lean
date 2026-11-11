module
public import ProjectiveRatioOverlapEquations318
public import PELOriginalLevelTwoSchemeMorphism318
public import PELOriginalCandidateIntegral318
public section
noncomputable section
namespace PELOriginalProjectiveRatioInputs318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalLevelTheta318
open PELOriginalAllLevelProjectiveMap318 PELOriginalReducedProjectiveCandidate318
open PELOriginalCandidateComplexPoints318 PELOriginalProperComplexCandidate318
open ProjectivePreimageRegularRatios318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- Every actual complex scheme point of the whole candidate has its
original torus representative, with literal equality of morphisms. -/
theorem point_representative (p : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ)
    (hp : p ≫ structureMap τ hτ = 𝟙 _) :
    ∃ q : Base τ, p = candidateComplexPoint τ hτ q := by
  obtain ⟨j,z,hz,he⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ p hp
  refine ⟨projection (P τ) z,?_⟩
  rw [he,PELOriginalChartSchemePointIdentity318.chart_point]

/-- Full point formula for the genuine original cubic closed immersion. -/
theorem cubic_point_model (p : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ)
    (hp : p ≫ structureMap τ hτ = 𝟙 _) :
    ∃ v : Label 3 → ℂ, ∃ hv : ∃ i,v i≠0,
      p ≫ inclusion τ hτ = ComplexProjectiveSchemePoint318.point v hv := by
  obtain ⟨q,rfl⟩ := point_representative τ hτ p hp
  exact ⟨baseVector τ hτ 1 q,PELOriginalProjectiveCandidatePoints318.actual_coordinate_nonzero τ hτ q,
    candidateComplexPoint_inclusion τ hτ q⟩

/-- Full point formula for the independently constructed global level-two
scheme map. It is not an assumed embedding or a projective point map. -/
theorem quadratic_point_model (p : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ)
    (hp : p ≫ structureMap τ hτ = 𝟙 _) :
    ∃ v : Label 2 → ℂ, ∃ hv : ∃ i,v i≠0,
      p ≫ PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ =
        ComplexProjectiveSchemePoint318.point v hv := by
  obtain ⟨q,rfl⟩ := point_representative τ hτ p hp
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  exact ⟨baseVector τ hτ 0 (projection (P τ) z),
    PELOriginalLevelTwoSchemePoint318.base_nonzero τ hτ _,
    PELOriginalLevelTwoSchemeMorphism318.original_point_action τ hτ z⟩

abbrev cubicOpen (j : Label 3) := sourceOpen (inclusion τ hτ) j
abbrev quadraticOpen (s : Label 2) :=
  sourceOpen (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) s
abbrev cubicRatio (j i : Label 3) := ratioSection (inclusion τ hτ) j i
abbrev quadraticRatio (s a : Label 2) :=
  ratioSection (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) s a

/-- Entire regular cubic transition, not just agreement at analytic points. -/
theorem cubic_transition (j k i : Label 3) :
    (ProjectiveRatioOverlapEquations318.left (inclusion τ hτ) j k).appTop (cubicRatio τ hτ j i) =
    (ProjectiveRatioOverlapEquations318.right (inclusion τ hτ) j k).appTop (cubicRatio τ hτ k i) *
      (ProjectiveRatioOverlapEquations318.left (inclusion τ hτ) j k).appTop (cubicRatio τ hτ j k) :=
  ProjectiveRatioOverlapEquations318.transition _ (structureMap τ hτ)
    (inclusion_over τ hτ) (cubic_point_model τ hτ) j k i

theorem cubic_transition_isUnit (j k : Label 3) :
    IsUnit ((ProjectiveRatioOverlapEquations318.left (inclusion τ hτ) j k).appTop
      (cubicRatio τ hτ j k)) :=
  ProjectiveRatioOverlapEquations318.transition_isUnit _ (structureMap τ hτ)
    (inclusion_over τ hτ) (cubic_point_model τ hτ) j k

/-- Entire regular quadratic transition on all scheme primes of the
actual inverse-image intersection. -/
theorem quadratic_transition (s t a : Label 2) :
    (ProjectiveRatioOverlapEquations318.left (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) s t).appTop
      (quadraticRatio τ hτ s a) =
    (ProjectiveRatioOverlapEquations318.right (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) s t).appTop
      (quadraticRatio τ hτ t a) *
    (ProjectiveRatioOverlapEquations318.left (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) s t).appTop
      (quadraticRatio τ hτ s t) :=
  ProjectiveRatioOverlapEquations318.transition _ (structureMap τ hτ)
    (PELOriginalLevelTwoSchemeMorphism318.over_complex τ hτ) (quadratic_point_model τ hτ) s t a

theorem quadratic_transition_isUnit (s t : Label 2) :
    IsUnit ((ProjectiveRatioOverlapEquations318.left (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) s t).appTop
      (quadraticRatio τ hτ s t)) :=
  ProjectiveRatioOverlapEquations318.transition_isUnit _ (structureMap τ hτ)
    (PELOriginalLevelTwoSchemeMorphism318.over_complex τ hτ) (quadratic_point_model τ hτ) s t
end PELOriginalProjectiveRatioInputs318
