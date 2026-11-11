module
public import PELOriginalEveryPointSmoothNeighborhood318
public import SmoothFromComplexPointNeighborhoods318
public section
noncomputable section
namespace PELOriginalCandidateSmooth318
open AlgebraicGeometry CategoryTheory
open PELOriginalProperComplexCandidate318 PELOriginalCandidateAffineCharts318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The SAME original reduced projective theta candidate is smooth
OVER ITS ACTUAL complex structure map. Every boundary is covered by
produced whole-ring derivative opens, and closed-point descent covers
all scheme points, not merely the analytic point set. -/
theorem smooth : Smooth (structureMap τ hτ) := by
  apply SmoothFromComplexPointNeighborhoods318.smooth (structureMap τ hτ)
  intro p hp
  obtain ⟨j,d,ho,hs,u,hu⟩ :=
    PELOriginalEveryPointSmoothNeighborhood318.every_complex_point τ hτ p hp
  exact ⟨Spec (CommRingCat.of (Localization.Away d)),
    PELOriginalDerivativeOpenCharts318.inclusion τ hτ j d,ho,hs,u,hu⟩
end PELOriginalCandidateSmooth318
