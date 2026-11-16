module
public import PELOriginalTorusPointAddEquiv318
public import PELOriginalCandidateSmooth318
public import PELOriginalCandidateIntegral318
public section
noncomputable section
namespace PELOriginalProperSmoothGroup318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The SAME scheme representing the constructed commutative group
functor is proper and smooth over its actual complex base, and integral
and connected as a whole scheme. Each property is supplied by its actual
producer; none is inferred from the analytic point-group equivalence. -/
theorem geometric_properties :
    IsProper (π τ hτ) ∧ Smooth (π τ hτ) ∧ IsIntegral (candidate τ hτ) ∧
      ConnectedSpace (candidate τ hτ) := by
  refine ⟨inferInstance,PELOriginalCandidateSmooth318.smooth τ hτ,
    PELOriginalCandidateIntegral318.integral τ hτ,?_⟩
  letI : IrreducibleSpace (candidate τ hτ) := PELOriginalCandidateIntegral318.irreducible τ hτ
  infer_instance

/-- Exact representing-object identity: the proper smooth group uses
the original candidate and the original complex structure map. -/
lemma representing_scheme :
    (PELOriginalRepresentedGroupFunctor318.candidateOver τ hτ).left=candidate τ hτ := rfl
lemma representing_base :
    (PELOriginalRepresentedGroupFunctor318.candidateOver τ hτ).hom=π τ hτ := rfl
end PELOriginalProperSmoothGroup318
