module
public import PELOriginalAffineChartDimension318
public import PELOriginalCandidateNineChartCover318
public import OpenCoverKrullBound318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section
namespace PELOriginalCandidateDimension318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)
/-- The entire SAME algebraic candidate has topological Krull dimension
at most two. The cover is the genuine nine-chart cover of ALL scheme
primes, not only the original analytic image or its complex points. -/
theorem actual_dimension_le_two:topologicalKrullDim (candidate τ hτ)≤2:=by
  apply OpenCoverKrullBound318.dimension_le
    (fun j:Label 3=>Spec (CommRingCat.of (CoordinateChart τ hτ j)))
    (fun j=>(chartMap τ hτ j).base)
    (fun j=>(chartMap τ hτ j).isOpenEmbedding)
  · intro p
    obtain ⟨j,hj⟩:=charts_cover τ hτ p
    refine ⟨j,(actualChartIso τ hτ j).inv ⟨p,hj⟩,?_⟩
    exact congrArg (candidateChart τ hτ j).ι
      (Iso.inv_hom_id_apply (actualChartIso τ hτ j) ⟨p,hj⟩)
  · intro j
    change topologicalKrullDim (PrimeSpectrum (CoordinateChart τ hτ j))≤2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact PELOriginalAffineChartDimension318.actual_chart_dimension_le_two τ hτ j
end PELOriginalCandidateDimension318
