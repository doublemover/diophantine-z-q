module
public import PELOriginalCubeGeneratingSections318
public import ProjectiveSubopenVectorMorphism318
public section
noncomputable section
namespace PELOriginalCubeClosedImmersion318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalProperComplexCandidate318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalMixedRatioCover318
open PELOriginalProjectiveRatioInputs318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ
local instance standardGrading : GradedAlgebra
    (ComplexProjectiveMarkerPoint318.grading (ι := Label 3)) := MvPolynomial.gradedAlgebra

/-- The normalized coefficient vector of the actual nine tensor-cube
sections generates the entire regular-function ring of each mixed chart. -/
lemma coefficient_span (a : NonemptyIndex τ hτ) :
    Ideal.span (Set.range (cubic τ hτ a.val)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self a.val.1))
  rw [cubic_self]
  exact isUnit_one

/-- Actual regular projective morphism defined by the coefficients of
the nine global sections in the produced tensor-cube frame. -/
@[expose] def localMorphism (a : NonemptyIndex τ hτ) :
    (opens τ hτ a).toScheme ⟶ PELOriginalReducedProjectiveCandidate318.ambient :=
  ComplexProjectiveRegularVector318.morphism
    ((opens τ hτ a).ι ≫ structureMap τ hτ)
    (cubic τ hτ a.val) (coefficient_span τ hτ a)

/-- On EVERY full mixed scheme chart, the actual section-defined
projective map is precisely the SAME original closed immersion. -/
theorem localMorphism_eq (a : NonemptyIndex τ hτ) :
    localMorphism τ hτ a = (opens τ hτ a).ι ≫ inclusion τ hτ :=
  ProjectiveSubopenVectorMorphism318.morphism_eq (inclusion τ hτ)
    (structureMap τ hτ) (inclusion_over τ hτ) (cubic_point_model τ hτ)
    (opens τ hτ a) a.val.1 inf_le_left

/-- The local section-defined maps agree as whole SCHEME morphisms
on all mixed intersections, including nonclosed primes. -/
theorem localMorphism_overlap (a b : NonemptyIndex τ hτ) :
    toLeft τ hτ a.val b.val ≫ localMorphism τ hτ a =
      toRight τ hτ a.val b.val ≫ localMorphism τ hτ b := by
  rw [localMorphism_eq,localMorphism_eq]
  simp only [toLeft,toRight,←Category.assoc,Scheme.homOfLE_ι]

/-- Concrete positive-power projective realization: the THIRD actual
tensor power has nine globally generating sections, their normalized
regular maps cover the entire scheme, and these maps realize a genuine
closed immersion into P^8. This does not introduce an unverified
abstract ampleness or polarization predicate. -/
theorem positive_power_closed_immersion :
    Epi (PELOriginalCubeGeneratingSections318.presentation τ hτ) ∧
    ((⊤ : (candidate τ hτ).Opens) ≤ ⨆ a : NonemptyIndex τ hτ,opens τ hτ a) ∧
    ∃ f : candidate τ hτ ⟶ PELOriginalReducedProjectiveCandidate318.ambient,
      IsClosedImmersion f ∧ f = inclusion τ hτ ∧
      ∀ a : NonemptyIndex τ hτ, localMorphism τ hτ a = (opens τ hτ a).ι ≫ f := by
  refine ⟨inferInstance,coversTop τ hτ,inclusion τ hτ,inferInstance,rfl,?_⟩
  exact localMorphism_eq τ hτ
end PELOriginalCubeClosedImmersion318
